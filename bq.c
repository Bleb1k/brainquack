/* Copyright 2025 owl

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License. */

#include <assert.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/ucontext.h>
#include <unistd.h>

#define cvector_clib_malloc emalloc
#define cvector_clib_realloc erealloc
#include "cvector.h"

//#define PRINT_BUT_DONT_EXEC

#define code_trap() code_append("\xcc")

#define likely(x) (__builtin_expect(!!(x), 1))
#define unlikely(x) (__builtin_expect(!!(x), 0))
#define likeliness(x, l) (__builtin_expect_with_probability(!!(x), 0, l))
#define hot __attribute((hot))
#define cold __attribute((cold))
#define noreturn __attribute((noreturn))

static char  *tape, *tapestart, *tapeguardpages[2];
static size_t realtapesize;

typedef enum { OP_MOVE, OP_ADD, OP_OUTPUT, OP_INPUT, OP_JUMP_RIGHT, OP_JUMP_LEFT, OP_SET, OP_ADD_TO, OP_MOVE_UNTIL } Opcode;

static const char *const nops[] = {
	"\x90",                                    // nop
	"\x66\x90",                                // xchg ax,ax
	"\x0f\x1f\x00",                            // nop DWORD PTR [eax]
	"\x0f\x1f\x40\x00",                        // nop DWORD PTR [eax+0x0]
	"\x0f\x1f\x44\x00\x00",                    // nop DWORD PTR [eax+eax*1+0x0]
	"\x66\x0f\x1f\x44\x00\x00",                // nop WORD PTR [eax+eax*1+0x0]
	"\x0f\x1f\x80\x00\x00\x00\x00",            // nop DWORD PTR [eax+0x0]
	"\x0f\x1f\x84\x00\x00\x00\x00\x00",        // nop DWORD PTR [eax+eax*1+0x0]
	"\x66\x0f\x1f\x84\x00\x00\x00\x00\x00",    // nop WORD PTR [eax+eax*1+0x0]
	"\x66\x2e\x0f\x1f\x84\x00\x00\x00\x00\x00" // nop WORD PTR cs:[eax+eax*1+0x0]
};

typedef struct {
	Opcode op;
	int    arg;
	int    off;
} Instr;

static inline size_t
max(size_t a, size_t b)
{
	return a > b ? a : b;
}

static void cold
usage(char *argv0)
{
	fprintf(stderr, "usage: %s [file]\n", argv0);
	exit(1);
}

static void noreturn cold
die(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);

	if (*fmt && fmt[strlen(fmt) - 1] == ':') {
		fputc(' ', stderr);
		perror(NULL);
	} else {
		fputc('\n', stderr);
	}

	exit(1);
}

static void *
emalloc(size_t size)
{
	void *p;

	if unlikely (!(p = malloc(size)))
		die("emalloc:");

	return p;
}

static void *
erealloc(void *ptr, size_t size)
{
	void *p;

	if unlikely (!(p = realloc(ptr, size)))
		die("erealloc:");

	return p;
}

static bool hot
isop(char c)
{
	return strchr("><+-.,[]", c);
}

static bool
isstdincomplete(struct stat *st)
{
	if (isatty(STDIN_FILENO))
		return false;

	if (fstat(STDIN_FILENO, st) < 0)
		return false;

	if (S_ISREG(st->st_mode))
		return true;

	if (S_ISFIFO(st->st_mode)) {
		struct pollfd pfd = { .fd = STDIN_FILENO, .events = POLLIN };
		poll(&pfd, 1, 0);
		return pfd.revents & POLLHUP;
	}

	return false;
}

static void
handler(int signum, siginfo_t *si, void *ucontext)
{
	size_t pagesize = getpagesize();
	void  *addr     = si->si_addr;

	if unlikely (!(((addr >= (void *)tapeguardpages[1]) && (addr < (void *)(tapeguardpages[1] + pagesize))) ||
	               ((addr >= (void *)tapeguardpages[0]) && (addr < (void *)(tapeguardpages[0] + pagesize))))) {
		SIG_DFL(signum);
		__builtin_unreachable();
	}

	munmap(tapeguardpages[0], pagesize);
	munmap(tapeguardpages[1], pagesize);

	char *oldtapestart = tapestart;
	char *newtapestart = (char *)mremap(tapestart, realtapesize + pagesize * 2, realtapesize * 2 + pagesize * 2, MREMAP_MAYMOVE);
	if (newtapestart == MAP_FAILED)
		die("could not resize tape memory:");

	tapestart = newtapestart;
	tape      = tapestart + pagesize + realtapesize / 2;
	realtapesize *= 2;

	if likely (tapestart != oldtapestart) {
		ucontext_t *uctx = ucontext;
		uctx->uc_mcontext.gregs[REG_RBX] =
				(greg_t)tape + uctx->uc_mcontext.gregs[REG_RBX] - (uintptr_t)(oldtapestart + pagesize + realtapesize / 4);
	}

	tapeguardpages[1] = tapestart + realtapesize + pagesize;
	if unlikely (mprotect(tapeguardpages[1], pagesize, PROT_NONE) < 0)
		die("could not protect tape memory overflow guard page:");

	tapeguardpages[0] = tapestart;
	if unlikely (mprotect(tapeguardpages[0], pagesize, PROT_NONE) < 0)
		die("could not protect tape memory underflow guard page:");
}

int
main(int argc, char *argv[])
{
	if unlikely (argc != 2)
		usage(argv[0]);

	int fd = open(argv[1], O_RDONLY);
	if unlikely (fd < 0)
		die("cannot access '%s':", argv[1]);

	struct stat st;
	fstat(fd, &st);

	char *txt = emalloc(st.st_size);
	read(fd, txt, st.st_size);
	close(fd);

	struct stat stdin_st;
	bool        stdin_complete = isstdincomplete(&stdin_st);
	char       *stdin_txt      = NULL;

	if (stdin_complete) {
		if (S_ISREG(stdin_st.st_mode)) {
			stdin_txt = emalloc(stdin_st.st_size);
			read(STDIN_FILENO, stdin_txt, stdin_st.st_size);
		} else if (S_ISFIFO(stdin_st.st_mode)) {
			int n;
			ioctl(STDIN_FILENO, FIONREAD, &n);
			stdin_txt = emalloc(n + 1);
			read(STDIN_FILENO, stdin_txt, n);
			stdin_txt[n] = '\0';
		} else {
			stdin_complete = false;
		}
	}

	cvector(Instr) instrs = NULL;
	cvector_reserve(instrs, (size_t)st.st_size);

	for (char *s = txt; likely(*s); s++) {
		static int offset     = 0;
		static int loop_depth = 0;
		Instr      instr;
		switch (*s) {
		case '>':
		case '<': {
			int n = 0;
			for (s--; s[1] == '>' || s[1] == '<' || !isop(s[1]); s++)
				if (s[1] == '>')
					n++;
				else if (s[1] == '<')
					n--;

			if likely (n != 0) {
				instr = (Instr){ OP_MOVE, n, 0 };
				cvector_push_back(instrs, instr);

				if (loop_depth == 0)
					offset += n;
			}

			break;
		}
		case '+':
		case '-': {
			int n = 0;
			for (s--; s[1] == '+' || s[1] == '-' || !isop(s[1]); s++)
				if (s[1] == '+')
					n++;
				else if (s[1] == '-')
					n--;

			if likely (n != 0) {
				Instr *last = cvector_end(instrs);

				if (last && last->op == OP_SET) {
					last->arg += n;
				} else {
					instr = (Instr){ OP_ADD, n, offset };
					cvector_push_back(instrs, instr);
				}
			}

			break;
		}
		case '.':
			instr.op  = OP_OUTPUT;
			instr.off = offset;
			cvector_push_back(instrs, instr);
			break;
		case ',':
			instr.op  = OP_INPUT;
			instr.off = offset;
			cvector_push_back(instrs, instr);
			break;
		case '[':
			loop_depth += 1;
			instr.op  = OP_JUMP_RIGHT;
			instr.off = offset;
			cvector_push_back(instrs, instr);
			break;
		case ']': {
			loop_depth -= 1;
			size_t len = cvector_size(instrs);

			// [-] or [+]
			if (len >= 2 && instrs[len - 1].op == OP_ADD && instrs[len - 1].arg & 1 && instrs[len - 2].op == OP_JUMP_RIGHT) {
				cvector_set_size(instrs, len - 2);
				instr = (Instr){ OP_SET, 0, offset };
				cvector_push_back(instrs, instr);
				break;
			}

			// [->+<] or [-<+>]
			if (len >= 5 && instrs[len - 1].op == OP_MOVE && instrs[len - 2].op == OP_ADD && instrs[len - 2].arg == 1 &&
			    instrs[len - 3].op == OP_MOVE && instrs[len - 4].op == OP_ADD && instrs[len - 4].arg == -1 &&
			    instrs[len - 1].arg == -instrs[len - 3].arg && instrs[len - 5].op == OP_JUMP_RIGHT) {
				cvector_set_size(instrs, len - 5);
				instr = (Instr){ OP_ADD_TO, instrs[len - 3].arg, offset };
				cvector_push_back(instrs, instr);
				instr = (Instr){ OP_SET, 0, offset };
				cvector_push_back(instrs, instr);
				break;
			}

			// [>] or [<]
			if (len >= 2 && instrs[len - 1].op == OP_MOVE && instrs[len - 2].op == OP_JUMP_RIGHT) {
				cvector_set_size(instrs, len - 2);
				instr = (Instr){ OP_MOVE_UNTIL, instrs[len - 1].arg, offset };
				cvector_push_back(instrs, instr);
				break;
			}

			instr.op  = OP_JUMP_LEFT;
			instr.off = offset;
			cvector_push_back(instrs, instr);
			break;
		}
		default: break;
		}
	}

	free(txt);

	cvector(unsigned char) code = NULL;
	cvector_reserve(code, max(cvector_size(instrs) * 5, 128));

	cvector(uintptr_t) jmps = NULL;
	cvector_reserve(jmps, max(cvector_size(instrs) / 20, 16));

	cvector(uintptr_t) putcharpatches = NULL;
	cvector_reserve(putcharpatches, max(cvector_size(instrs) / 100, 64));

	cvector(uintptr_t) getcharpatches = NULL;
	cvector_reserve(getcharpatches, max(cvector_size(instrs) / 200, 32));

#define code_append(snip_)                                       \
	do {                                                         \
		size_t snip_size_ = sizeof snip_ / sizeof *snip_ - 1;    \
		cvector_reserve(code, cvector_size(code) + snip_size_);  \
		memcpy(code + cvector_size(code), snip_, snip_size_);    \
		cvector_set_size(code, cvector_size(code) + snip_size_); \
	} while (0)

#define code_align(align)                                                  \
	do {                                                                   \
		if (align <= 1)                                                    \
			break;                                                         \
		uintptr_t cur = (uintptr_t)(code + cvector_size(code));            \
		size_t    pad = ((align) - (cur & ((align) - 1))) & ((align) - 1); \
		size_t    off = cvector_size(code);                                \
		cvector_reserve(code, off + pad);                                  \
		size_t i = 0;                                                      \
		while (pad > 0) {                                                  \
			size_t nopsize = pad > 10 ? 10 : pad;                          \
			memcpy(code + off + i, nops[nopsize - 1], nopsize);            \
			i += nopsize;                                                  \
			pad -= nopsize;                                                \
		}                                                                  \
		cvector_set_size(code, off + i);                                   \
	} while (0)

	if (stdin_complete) {
		code_append("\x49\xbf\x00\x00\x00\x00\x00\x00\x00\x00"); // movabs r15, imm64
		*(void **)(code + cvector_size(code) - 8) = stdin_txt;
	}

	const char snip[] = "\x49\xbd\x00\x00\x00\x00\x00\x00\x00\x00" // movabs r13, imm64
						"\x49\xbe\x00\x00\x00\x00\x00\x00\x00\x00" // movabs r14, imm64
						"\x48\x89\xfb";                            // mov rbx, rdi

	code_append(snip);
	*(void **)(code + cvector_size(code) - 21) = stdin;
	*(void **)(code + cvector_size(code) - 11) = stdout;

	size_t icacheline                          = sysconf(_SC_LEVEL1_ICACHE_LINESIZE);
	code_align(icacheline);

#define insert_modrf(op_, rf_)                                                      \
	do {                                                                            \
		if (instr.off == 0) {                                                       \
			cvector_push_back(code, ((op_) << 3) + (rf_));                          \
		} else if (instr.off >= CHAR_MIN && instr.off <= CHAR_MAX) {                \
			code_append(((char[]){ '\x40' + ((op_) << 3) + (rf_), instr.off, 0 })); \
		} else if (instr.off >= INT_MIN && instr.off <= INT_MAX) {                  \
			code_append(((char[]){ '\x80' + ((op_) << 3) + (rf_),                   \
			                       instr.off & 0xff,                                \
			                       (instr.off >> 8) & 0xff,                         \
			                       (instr.off >> 16) & 0xff,                        \
			                       (instr.off >> 24) & 0xff,                        \
			                       0 }));                                           \
		}                                                                           \
                                                                                    \
	} while (0)
	for (size_t i = 0; likely(i < cvector_size(instrs)); i++) {
		Instr instr = instrs[i];

		switch (instr.op) {
		case OP_MOVE:
			if (cvector_size(jmps) > 0) {
				if (instr.arg == 1)
					code_append("\x48\xff\xc3"); // inc rbx
				else if (instr.arg == -1)
					code_append("\x48\xff\xcb"); // dec rbx
				else if (instr.arg > 0) {
					unsigned int n = instr.arg;

					if likely (n <= UCHAR_MAX) {
						code_append("\x48\x83\xc3\x00"); // add rbx, imm8
						code[cvector_size(code) - 1] = n;
					} else {
						code_append("\x48\x81\xc3\x00\x00\x00\x00"); // add rbx, imm32
						*(unsigned int *)(code + cvector_size(code) - 4) = n;
					}
				} else if (instr.arg < 0) {
					unsigned int n = -instr.arg;

					if (n <= UCHAR_MAX) {
						code_append("\x48\x83\xeb\x00"); // sub rbx, imm8
						code[cvector_size(code) - 1] = n;
					} else {
						code_append("\x48\x81\xeb\x00\x00\x00\x00"); // sub rbx, imm32
						*(unsigned int *)(code + cvector_size(code) - 4) = n;
					}
				}
			}
			break;
		case OP_ADD: {
			short n = instr.arg % 256;

			if (n == 1 || n == -1) {
				cvector_push_back(code, '\xfe'); // inc/dec BYTE PTR [rbx] + off8/32
				insert_modrf(n == -1, 3);
			} else {
				cvector_push_back(code, '\x80'); // add BYTE PTR [rbx] + off8/32, imm8
				insert_modrf(n < 0 ? 5 : 0, 3);
				cvector_push_back(code, n < 0 ? -n : n);
			}

			break;
		}
		case OP_OUTPUT: {
			// const char snip[] = "\x48\x0f\xbe\x3b"      // movsx rdi, BYTE PTR [rbx] + off8/32
			// "\xe8\x00\x00\x00\x00"; // call  rel32

			code_append("\x48\x0f\xbe");
			insert_modrf(7, 3);

			code_append("\xe8\x00\x00\x00\x00");
			cvector_push_back(putcharpatches, cvector_size(code) - 4);
			break;
		}
		case OP_INPUT: {
			if (!stdin_complete) {
				const char snip[] = "\xe8\x00\x00\x00\x00" // call rel32
									"\x88";                // mov  BYTE PTR [rbx] + off8/32, al
				cvector_push_back(getcharpatches, cvector_size(code) + 1);
				code_append(snip);
				insert_modrf(0, 3);
			} else {
				const char snip[] = "\x41\x8a\07" // mov al, BYTE PTR [r15]
									"\x88";       // mov BYTE PTR [rbx] + off8/32, al
				code_append(snip);
				insert_modrf(0, 3);
				code_append("\x49\xff\xc7"); // inc r15
			}
			break;
		}
		case OP_JUMP_RIGHT: {
			size_t cost         = 0;
			size_t jmpstraverse = cvector_size(jmps) + 1;
			for (size_t j = i; jmpstraverse && likely(j < cvector_size(instrs)); j++)
				switch (instrs[j].op) {
				case OP_MOVE: cost += 3; break;
				case OP_ADD: cost += 1; break;
				case OP_OUTPUT: cost += 40; break;
				case OP_INPUT: cost += 35; break;
				case OP_JUMP_RIGHT: cost += 10; break;
				case OP_JUMP_LEFT:
					cost += 8;
					jmpstraverse--;
					break;
				case OP_SET: cost += 2; break;
				case OP_ADD_TO: cost += 10; break;
				case OP_MOVE_UNTIL: cost += 10; break;
				}

			const char snip[] = "\x0f\x84"          // jz rel32
								"\x0f\x1f\x40\x00"; // nop DWORD PTR [eax+0x0]

			code_align(icacheline >> ((cvector_size(jmps) + 1) * cost / 50));
			cvector_push_back(code, '\x80'); // cmp BYTE PTR [rbx] + off8/32, 0
			insert_modrf(7, 3);
			cvector_push_back(code, 0);
			code_append(snip);
			cvector_push_back(jmps, cvector_size(code));
			break;
		}
		case OP_JUMP_LEFT: {
			cvector_push_back(code, '\x80'); // cmp BYTE PTR [rbx] + off8/32, 0
			insert_modrf(7, 3);
			cvector_push_back(code, 0);

			if unlikely (cvector_size(jmps) == 0)
				die("mismatched ]");

			size_t jmp = jmps[cvector_size(jmps) - 1];
			cvector_pop_back(jmps);

			{
				int rel = jmp - (cvector_size(code) + 2);

				if likely (rel >= CHAR_MIN && rel <= CHAR_MAX) {
					code_append("\x75\x00"); // jnz rel8
					code[cvector_size(code) - 1] = rel;
				} else {
					code_append("\x0f\x85\x00\x00\x00\x00"); // jnz rel32
					*(int *)(code + cvector_size(code) - 4) = rel - 4;
				}
			}

			{
				int rel = cvector_size(code) - jmp;

				if likely (rel >= CHAR_MIN && rel <= CHAR_MAX) {
					code[jmp - 6] = 0x74; // jz rel8
					code[jmp - 5] = rel + 4;
				} else {
					*(int *)(code + jmp - 4) = rel; // rel32
				}
			}

			break;
		}
		case OP_SET: {
			char bin_instr = '\xc6'; // mov BYTE PTR [rbx] + off8/32, n
			char imm_size  = 1;
			if (instr.arg >= CHAR_MIN && instr.arg <= CHAR_MAX) {
			} else if (instr.arg >= SHRT_MIN && instr.arg <= SHRT_MAX) {
				bin_instr = '\xc7';
				imm_size  = 2;
			} else {
				bin_instr = '\xc7';
				imm_size  = 4;
			}
			cvector_push_back(code, bin_instr);
			insert_modrf(0, 3);
			for (char i = imm_size; i--;)
				cvector_push_back(code, '\x00');
			code[cvector_size(code) - imm_size] = imm_size == 1 ? (char)instr.arg : imm_size == 2 ? (short)instr.arg : instr.arg;
			break;
		}
		case OP_ADD_TO: {
			// if likely (instr.arg + instr.off >= CHAR_MIN && instr.arg + instr.off <= CHAR_MAX) {
			// 	const char snip[] = "\x8a\x03"      // mov al, BYTE PTR [rbx]
			// 						"\x00\x43\x00"  // add BYTE PTR [rbx + disp8], al
			// 						"\xc6\x03\x00"; // mov BYTE PTR [rbx], 0

			// 	code_append(snip);
			// 	code[cvector_size(code) - 4] = instr.arg;
			// } else {
			// 	const char snip[] = "\x8a\x03"                 // mov al, BYTE PTR [rbx]
			// 						"\x00\x83\x00\x00\x00\x00" // add BYTE PTR [rbx + disp32], al
			// 						"\xc6\x03\x00";            // mov BYTE PTR [rbx], 0

			// 	code_append(snip);
			// 	*(int *)(code + cvector_size(code) - 7) = instr.arg;
			// }
			cvector_push_back(code, '\x8a'); // mov al, BYTE PTR [rbx] + off8/32
			insert_modrf(0, 3);
			cvector_push_back(code, '\x00'); // add BYTE_PTR [rbx] + off8/32
			insert_modrf(0, 3);
			break;
		}
		case OP_MOVE_UNTIL:
			if (instr.arg == 1 || instr.arg == -1) {
				// const char snip[] = "\x80\x3b\x00" // cmp BYTE PTR [rbx], 0
				// 					"\x74\x05"     // je   5
				// 					"\x48\xff\xc3" // inc rbx
				// 					"\xeb\xf6";    // jmp -10

				// code_append(snip);
				uintptr_t start = cvector_size(code);
				cvector_push_back(code, '\x80');
				insert_modrf(7, 3);
				code_append("\x74\x05"
				            "\x48\xff");
				cvector_push_back(code, instr.arg == 1 ? '\xc3' : '\xcb');
				code_append("\xeb\x00"); // jump back insert
				code[cvector_size(code) - 1] = cvector_size(code) - start;
			} else if (instr.arg > 1 || instr.arg < -1) {
				bool         neg   = instr.arg < -1;
				unsigned int n     = instr.arg * -neg;
				uintptr_t    start = cvector_size(code);

				cvector_push_back(code, '\x80');
				insert_modrf(7, 3);
				code_append("\x00"
				            "\x74\x06"
				            "\x48");
				if likely (n <= UCHAR_MAX) {
					// const char snip[] = "\x80\x3b\x00"     // cmp BYTE PTR [rbx], 0
					// 					"\x74\x06"         // je  +6
					// 					"\x48\x83\xc3\x00" // add rbx, imm8
					// 					"\xeb\xf5";        // jmp -11

					// code_append(snip);

					code_append(((char[]){ '\x83', neg ? '\xeb' : '\xc3', n, '\xeb', 0 })); // jump back insert
																							// code[cvector_size(code) - 3] = n;
				} else {
					// const char snip[] = "\x80\x3b\x00"                 // cmp BYTE PTR [rbx], 0
					// 					"\x74\x09"                     // je  +9
					// 					"\x48\x81\xc3\x00\x00\x00\x00" // add rbx, imm32
					// 					"\xeb\xf2";                    // jmp -14

					// code_append(snip);
					code_append(((char[]){ '\x81', neg ? '\xeb' : '\xc3', 0, 0, 0, 0, '\xeb', 0 })); // jump back insert
					*(unsigned int *)(code + cvector_size(code) - 6) = n;
				}
				code[cvector_size(code) - 1] = (char)(start - cvector_size(code));
			}
			break;
		}
	}

	if unlikely (cvector_size(jmps) != 0)
		die("unterminated [");

	cvector_free(instrs);
	cvector_free(jmps);

	code_append("\xc3"); // ret

	void *fn = mmap(NULL, cvector_size(code), PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	if unlikely (!fn)
		die("could not allocate executable memory:");

	for (size_t i = 0; i < cvector_size(putcharpatches); i++)
		*(int *)&code[putcharpatches[i]] = (uintptr_t)putchar_unlocked - ((uintptr_t)fn + putcharpatches[i] + 4);

	cvector_free(putcharpatches);

	for (size_t i = 0; i < cvector_size(getcharpatches); i++)
		*(int *)&code[getcharpatches[i]] = (uintptr_t)getchar_unlocked - ((uintptr_t)fn + getcharpatches[i] + 4);

	cvector_free(getcharpatches);

#ifdef PRINT_BUT_DONT_EXEC
	fwrite(code, cvector_size(code), 1, stdout);

	return 0;
#endif

	memcpy(fn, code, cvector_size(code));
	mprotect(fn, cvector_size(code), PROT_EXEC);
	cvector_free(code);

	size_t tapesize = 30000;
	size_t pagesize = getpagesize();
	realtapesize    = (tapesize + pagesize - 1) & ~(pagesize - 1);

	tapestart       = mmap(NULL, realtapesize * 2 + pagesize * 2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	if unlikely (!tapestart)
		die("could not allocate tape memory:");

	tape              = tapestart + pagesize + realtapesize / 2;

	tapeguardpages[1] = tapestart + realtapesize + pagesize;
	if unlikely (mprotect(tapeguardpages[1], pagesize, PROT_NONE) < 0)
		die("could not protect tape memory overflow guard page:");

	tapeguardpages[0] = tapestart;
	if unlikely (mprotect(tapeguardpages[0], pagesize, PROT_NONE) < 0)
		die("could not protect tape memory underflow guard page:");

	struct sigaction sa;
	sa.sa_sigaction = handler;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = SA_SIGINFO;
	if unlikely (sigaction(SIGSEGV, &sa, NULL) < 0)
		die("could not prepare tape memory guard page:");

	(*(void (**)(void *))&fn)(tape);
	// leak tape on purpose

	return 0;
}
