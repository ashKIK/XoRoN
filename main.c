#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

typedef DWORD64 D64;

#define NAME "XoRoN x64"

int __forceinline POPCNT(D64 p) {
    return _popcnt64(p);
}

static int BSF(D64 k) {
    DWORD idx = ~0;
    _BitScanForward64(&idx, k);
    return idx;
}


/**
static int BSF(D64 k) {
    return __builtin_ffsll(k) - 1;
}
*/

enum color {WC, BC, NOCL};
enum piece {P, N, B, R, Q, K, NOTP};
enum trans {NONE, UPPER, LOWER, EXACT};
enum files {FA, FB, FC, FD, FE, FF, FG, FH};
enum ranks {R1, R2, R3, R4, R5, R6, R7, R8};
enum types {NORMAL, CASTLE, EPCP, EPST, PMN, PMB, PMR, PMQ};
enum ptype {WP, BP, WN, BN, WB, BB, WR, BR, WQ, BQ, WK, BK, NOPC};
enum square {
    A1, B1, C1, D1, E1, F1, G1, H1, A2, B2, C2, D2, E2, F2, G2, H2,
    A3, B3, C3, D3, E3, F3, G3, H3, A4, B4, C4, D4, E4, F4, G4, H4,
    A5, B5, C5, D5, E5, F5, G5, H5, A6, B6, C6, D6, E6, F6, G6, H6,
    A7, B7, C7, D7, E7, F7, G7, H7, A8, B8, C8, D8, E8, F8, G8, H8,
    NOSQ
};

#define INFO_STRING             "info string "
#define BUILD_PROT					    "UCI"
#define BUILD_NUMBER				    "{196}"
#define BUILD_TAG					      "$ENV{BUILD_TAG}"
#define BUILD_BRANCH				    "{SSE4.2}"
#define MPLY						        64
#define INFINITY					      32767
#define MATESCORE					      32000
#define MEVAL						        29999
#define SQB(x)						      (1ull << (x))
#define PC(x, y)					      (((y) << 1) | (x))
#define FILE(x)						      ((x) & 7)
#define RANK(x)						      ((x) >> 3)
#define PCB(position, x, y)			((position)->CLB[x] & (position)->TPB[y])
#define TPONSQR(position, x)		(((position)->PCC[x]) >> 1)
#define KINGSQR(position, x)		((position)->KINGSQUARE[x])
#define L1ATT(o, x)					    attacks[0][x][((o) >> ((070 & (x)) + 1)) & 63]
#define L2ATT(o, x)					    attacks[1][x][((0x0101010101010101ull & ((o) >> ((x) & 7))) * 0x0204081020408000ull) >> 58]
#define L3ATT(o, x)					    attacks[2][x][(((o) & controlMask[2][x]) * 0x0202020202020202ull) >> 58]
#define L4ATT(o, x)					    attacks[3][x][(((o) & controlMask[3][x]) * 0x0202020202020202ull) >> 58]
#define ROOKATT(o, x)				    (L1ATT(o, x) | L2ATT(o, x))
#define BISHOPATT(o, x)				  (L3ATT(o, x) | L4ATT(o, x))
#define QUEENATT(o, x)				  ((L1ATT(o, x)| L2ATT(o, x)) | (L3ATT(o, x) | L4ATT(o, x)))

typedef struct {
    D64 KEYLCT, CLB[2], TPB[6], REPLIST[256];
    int PCC[64], KINGSQUARE[2], MATERIAL[2], PST[2];
    int SIDE, CAPFLAGS, ENPSQR, REVMOVE, HEAD;
} POST;

typedef struct {
    POST *position;
    int PHASE, TTMOVE, KM1, KM2, *NXT, *LAST, *BADPWN;
    int move[512], value[512], BAD[512];
} MOVES;

typedef struct {
    int TTP, CAPFLAGS, ENPSQR, REVMOVE;
    D64 KEYLCT;
} UNDO;

typedef struct {
    D64 KEYLCT;
    int DATE, move, score;
    unsigned char FLAGS, depth;
} DATA;

D64 RX(void);

int *genCaptures(POST *, int *), *genQuietPOS(POST *, int *);

/*  DATA  */

static DATA *transTable;

static D64 zobristPC[12][64], zobristCastle[16], zobristEnPassant[8], attacks[4][64][64], pawnAttacks[2][64];
static D64 controlMask[4][64], knightAttacks[64], kingAttacks[64], passedMask[2][64], adjacentMask[8];
static int PST[6][64], captureMask[64], history[12][64], killer[MPLY][2];

static const int passedBonus[2][8]  = {{0, 20, 25, 30, 35, 40, 45, 0},{0, 45, 40, 35, 30, 25, 20, 0}};
static const int pieceValue[7]      = {100, 330, 330, 530, 1000, 0, 0};

static int transTableSize, transTableMask, transTableDate, rootDepth, nodes, moveTime, pondering, killSearch, startTime;

/*  DATA END  */

static void buildTable(void) {
    int i, j, k, l, x, y;
    static const int dxn[4][2]		  = {{1, -1}, {16, -16}, {17, -17}, {15, -15}};
    static const int pawnMovesx[2][2] = {{15, 17}, {-17, -15}};
    static const int knightMovesx[8]  =	{-33, -31, -18, -14, 14, 18, 31, 33};
    static const int kingMovesx[8]	  =	{-17, -16, -15, -1, 1, 15, 16, 17};
    static const int line[8]		  = {0, 2, 4, 5, 5, 4, 2, 0};

    for (i = 0; i < 64; i++) {
        controlMask[0][i] = 0x00000000000000FFull << (i & 070);
        controlMask[1][i] = 0x0101010101010101ull << (i & 007);
        j = FILE(i) - RANK(i);
        if (j > 0) controlMask[2][i] = 0x8040201008040201ull >> (j << 3);
        else controlMask[2][i] = 0x8040201008040201ull << (-j << 3);
        j = FILE(i) - (R8 - RANK(i));
        if (j > 0) controlMask[3][i] = 0x0102040810204080ull << (j << 3);
        else controlMask[3][i] = 0x0102040810204080ull >> (-j << 3);
    }
    for (i = 0; i < 4; i++) {
        for (j = 0; j < 64; j++) {
            for (k = 0; k < 64; k++) {
                attacks[i][j][k] = 0;
                for (l = 0; l < 2; l++) {
                    for (x = ((j & 7) | ((j & ~7) << 1)) + dxn[i][l]; !((unsigned)(x) & 0x88); x += dxn[i][l]) {
                        y = (x & 7) | ((x & ~7) >> 1);
                        attacks[i][j][k] |= SQB(y);
                        if ((k << 1) & (1 << (i != 1 ? FILE(y) : RANK(y)))) break;
                    }
                }
            }
		}
	}
    for (i = 0; i < 2; i++) {
        for (j = 0; j < 64; j++) {
            for (pawnAttacks[i][j] = k = 0; k < 2; k++) {
                x = ((j & 7) | ((j & ~7) << 1)) + pawnMovesx[i][k];
                if (!((unsigned)(x) & 0x88)) pawnAttacks[i][j] |= SQB((x & 7) | ((x & ~7) >> 1));
            }
        }
	}
    for (i = 0; i < 64; i++) {
        knightAttacks[i] = 0;
        for (j = 0; j < 8; j++) {
            x = ((i & 7) | ((i & ~7) << 1)) + knightMovesx[j];
            if (!((unsigned)(x) & 0x88)) knightAttacks[i] |= SQB((x & 7) | ((x & ~7) >> 1));
        }
    }
    for (i = 0; i < 64; i++) {
        kingAttacks[i] = 0;
        for (j = 0; j < 8; j++) {
            x = ((i & 7) | ((i & ~7) << 1)) + kingMovesx[j];
            if (!((unsigned)(x) & 0x88)) kingAttacks[i] |= SQB((x & 7) | ((x & ~7) >> 1));
        }
    }
    for (i = 0; i < 64; i++) {
        passedMask[WC][i] = 0;
        for (j = FILE(i) - 1; j <= FILE(i) + 1; j++) {
            if ((FILE(i) == FA && j == -1) || (FILE(i) == FH && j == 8)) continue;
            for (k = RANK(i) + 1; k <= R8; passedMask[WC][i] |= SQB((k++ << 3) | j));
        }
    }
    for (i = 0; i < 64; i++) {
        passedMask[BC][i] = 0;
        for (j = FILE(i) - 1; j <= FILE(i) + 1; j++) {
            if ((FILE(i) == FA && j == -1) || (FILE(i) == FH && j == 8)) continue;
            for (k = RANK(i) - 1; k >= R1; passedMask[BC][i] |= SQB((k-- << 3) | j));
        }
    }
    for (i = 0; i < 8; i++) {
        adjacentMask[i] = 0;
        if (i > 0) adjacentMask[i] |= 0x0101010101010101ull << (i - 1);
        if (i < 7) adjacentMask[i] |= 0x0101010101010101ull << (i + 1);
    }
    for (i = 0; i < 64; i++) {
        j = line[FILE(i)] + line[RANK(i)];
        PST[P][i] = j << 1; PST[N][i] = j << 2;
        PST[B][i] = j << 1; PST[R][i] = line[FILE(i)];
        PST[Q][i] = j; PST[K][i] = j * 6;
    }
    for (i = 0; i < 64; captureMask[i++] = 15);
    captureMask[A1] = 13; captureMask[E1] = 12;
    captureMask[H1] = 14; captureMask[A8] = 7;
    captureMask[E8] = 3; captureMask[H8] = 11;
    for (i = 0; i < 12; i++)
        for (j = 0; j < 64; j++)
            zobristPC[i][j] = RX();
    for (i = 0; i < 16; zobristCastle[i++] = RX());
    for (i = 0; i < 8; zobristEnPassant[i++] = RX());

	for (i = 0; i < 12; i++)
		for (j = 0; j < 64; j++)
			history[i][j] = 0;
	for (i = 0; i < MPLY; i++) killer[i][0] = killer[i][1] = 0;
}

static void readLine(char *string, int k) {
    char *pointer;

    if (fgets(string, k, stdin) == NULL) exit(0);
    if ((pointer = strchr(string, '\n')) != NULL) *pointer = '\0';
}

static char *processChar(char *string, char *token) {
    for (;*string == ' '; string++);
    for (;*string != ' ' && *string != '\0'; *token++ = *string++);
    *token = '\0';
    return string;
}

static void uciControl(void) {
    char command[4096], token[80], *pointer;
    POST position[1];

	setbuf(stdin, NULL);
	setbuf(stdout, NULL);
    setPOS(position, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    allocateTT(128);
    for (;;) {
        readLine(command, sizeof(command));
        pointer = processChar(command, token);
        if (strcmp(token, "uci") == 0) {
            printf("id name "NAME"\n");
			printf("id author Ashutosh Gupta\n");
			printf("id country India\n");
            printf("option name Hash type spin default 128 min 4 max 1024\n");
            printf("option name Clear Hash type button\n");
			printf("option name Ponder type check default true\n");
			printf("option name UCI_EngineAbout type string default XoRoN Chess Engine\n");
            printf("uciok\n");
        }
		else if (strcmp(token, "isready") == 0)		printf("readyok\n");
        else if (strcmp(token, "setoption") == 0)	processOption(pointer);
        else if (strcmp(token, "position") == 0)	processPOS(position, pointer);
        else if (strcmp(token, "go") == 0)			processGO(position, pointer);
		else if (strcmp(token, "quit") == 0)		exit(0);
		fflush(stdout);
    }
}

__forceinline void processOption(char *pointer) {
    char token[80], name[80], value[80];

    pointer = processChar(pointer, token);
    name[0] = '\0';
    for (;;) {
        pointer = processChar(pointer, token);
        if (*token == '\0' || strcmp(token, "value") == 0) break;
        strcat(name, token);
		strcat(name, " ");
    }
    name[strlen(name) - 1] = '\0';
    if (strcmp(token, "value") == 0) {
        value[0] = '\0';
        for (;;) {
            pointer = processChar(pointer, token);
            if (*token == '\0') break;
            strcat(value, token);
			strcat(value, " ");
        }
        value[strlen(value) - 1] = '\0';
    }
    if (strcmp(name, "Hash") == 0) allocateTT(atoi(value));
    else if (strcmp(name, "Clear Hash") == 0) {
		DATA *data;
		transTableDate = 0;
		for (data = transTable; data < transTable + transTableSize; data++) {
			data->KEYLCT = data->DATE = data->move = data->score = data->FLAGS = data->depth = 0;
		}
	}
}

__forceinline void processPOS(POST *position, char *pointer) {
    char token[80], fen[80];
    UNDO undo[1];

    pointer = processChar(pointer, token);
    if (strcmp(token, "fen") == 0) {
        fen[0] = '\0';
        for (;;) {
            pointer = processChar(pointer, token);
            if (*token == '\0' || strcmp(token, "moves") == 0) break;
            strcat(fen, token);
			strcat(fen, " ");
        }
        setPOS(position, fen);
    } else {
        pointer = processChar(pointer, token);
        setPOS(position, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    }
    if (strcmp(token, "moves") == 0) {
        for (;;) {
            pointer = processChar(pointer, token);
            if (*token == '\0') break;
            doMove(position, convertMove(position, token), undo);
            if (position->REVMOVE == 0) position->HEAD = 0;
        }
	}
}

__forceinline void processGO(POST *position, char *pointer) {
    char token[80], bestmoveStr[6], ponderStr[6];
    int i, j, wtime, btime, winc, binc, movestogo, time, inc, pv[MPLY];

    moveTime = wtime = btime = -1;
    winc = binc = pondering = 0;
    movestogo = 40;
    for (;;) {
        pointer = processChar(pointer, token);
        if (*token == '\0')
            break;
        if (strcmp(token, "ponder") == 0) {
            pondering = 1;
        } else if (strcmp(token, "wtime") == 0) {
            pointer = processChar(pointer, token);
            wtime = atoi(token);
        } else if (strcmp(token, "btime") == 0) {
            pointer = processChar(pointer, token);
            btime = atoi(token);
        } else if (strcmp(token, "winc") == 0) {
            pointer = processChar(pointer, token);
            winc = atoi(token);
        } else if (strcmp(token, "binc") == 0) {
            pointer = processChar(pointer, token);
            binc = atoi(token);
        } else if (strcmp(token, "movestogo") == 0) {
            pointer = processChar(pointer, token);
            movestogo = atoi(token);
        }
    }
    time = position->SIDE == WC ? wtime : btime;
    inc = position->SIDE == WC ? winc : binc;
    if (time >= 0) {
        if (movestogo == 1) time -= min(800, time >> 4);
        moveTime = (time + inc * (movestogo - 1)) / movestogo;
        if (moveTime > time) moveTime = time;
        moveTime -= 10;
        if (moveTime < 0) moveTime = 0;
    }

	transTableDate = (transTableDate + 1) & 255;
	nodes = killSearch = 0;
	startTime = GetTickCount64();
	for (rootDepth = 1; rootDepth < 101; rootDepth++) {
		search(position, 0, -INFINITY, INFINITY, rootDepth, pv);
		if (killSearch) break;
	}

    convertStr(pv[0], bestmoveStr);
    if (pv[1]) {
        convertStr(pv[1], ponderStr);
        printf("bestmove %s ponder %s\n", bestmoveStr, ponderStr);
    } else printf("bestmove %s\n", bestmoveStr);
}

__forceinline void setPOS(POST *position, char *epd) {
	D64 KEYLCT;
    int i, j, PCC;
    static const char pieceChar[13] = "PpNnBbRrQqKk";

    position->CLB[0] = position->MATERIAL[0] = position->PST[0] =
	position->CLB[1] = position->MATERIAL[1] = position->PST[1] =
	position->TPB[0] = position->TPB[1] = position->TPB[2] =
	position->TPB[3] = position->TPB[4] = position->TPB[5] =
    position->CAPFLAGS = position->REVMOVE = position->HEAD = KEYLCT = 0;
    for (i = 56; i >= 0; i -= 8, epd++) {
        for (j = 0; j < 8; epd++) {
            if (*epd >= '1' && *epd <= '8') {
                for (PCC = 0; PCC < *epd - '0'; PCC++) {
                    position->PCC[i+j++] = NOPC;
                }
            } else {
                for (PCC = 0; pieceChar[PCC] != *epd; PCC++);
                position->PCC[i + j] = PCC;
                position->CLB[PCC & 1] ^= SQB(i + j);
                position->TPB[PCC >> 1] ^= SQB(i + j);
                if ((PCC >> 1) == K) position->KINGSQUARE[PCC & 1] = i + j;
                position->MATERIAL[PCC & 1] += pieceValue[PCC >> 1];
                position->PST[PCC & 1] += PST[PCC >> 1][i+j++];
            }
        }
    }
    if (*epd++ == 'w') position->SIDE = WC;
    else position->SIDE = BC; epd++;
    if (*epd == '-') epd++;
    else {
        if (*epd == 'K') { position->CAPFLAGS |= 1; epd++; }
        if (*epd == 'Q') { position->CAPFLAGS |= 2; epd++; }
        if (*epd == 'k') { position->CAPFLAGS |= 4; epd++; }
        if (*epd == 'q') { position->CAPFLAGS |= 8; epd++; }
    }
    epd++;
    if (*epd == '-') position->ENPSQR = NOSQ;
    else {
        position->ENPSQR = ((*(epd + 1) - '1') << 3) | (*epd - 'a');
        if (!(pawnAttacks[(position->SIDE) ^ 1][position->ENPSQR] & PCB(position, position->SIDE, P)))
            position->ENPSQR = NOSQ;
    }
    for (i = 0; i < 64; i++)
        if (position->PCC[i] != NOPC)
            KEYLCT ^= zobristPC[position->PCC[i]][i];
    KEYLCT ^= zobristCastle[position->CAPFLAGS];
    if (position->ENPSQR != NOSQ) KEYLCT ^= zobristEnPassant[FILE(position->ENPSQR)];
    if (position->SIDE == BC) KEYLCT ^= ~(0ull);
    position->KEYLCT = KEYLCT;
}

__forceinline void allocateTT(int mbsize) {
	DATA *data;
	transTableDate = 0;
    for (transTableSize = 2; transTableSize <= mbsize; transTableSize <<= 1);
    transTableSize = ((transTableSize / 2ull) << 20) / sizeof(DATA);
    transTableMask = transTableSize - 4;
    free(transTable);
    transTable = (DATA *) malloc(transTableSize * sizeof(DATA));
    for (data = transTable; data < transTable + transTableSize; data++) {
        data->KEYLCT = data->DATE = data->move = data->score = data->FLAGS = data->depth = 0;
    }
}

__forceinline int convertMove(POST *position, char *moveStr) {
    int from, to, type;

    from = ((moveStr[1] - '1') << 3) | (moveStr[0] - 'a');
    to = ((moveStr[3] - '1') << 3) | (moveStr[2] - 'a');
    type = NORMAL;
    if (TPONSQR(position, from) == K && abs(to - from) == 2) type = CASTLE;
    else if (TPONSQR(position, from) == P) {
        if (to == position->ENPSQR) type = EPCP;
        else if (abs(to - from) == 16) type = EPST;
        else if (moveStr[4] != '\0')
            switch (moveStr[4]) {
            case 'n': type = PMN; break;
            case 'b': type = PMB; break;
            case 'r': type = PMR; break;
            case 'q': type = PMQ; break;
            }
    }
    return (type << 12) | (to << 6) | from;
}

/*  SEARCH  */

__forceinline int getInput(void) {
    static int start = 0, pipe;
    static HANDLE handle;
    DWORD dword;

    if (!start) {
        start = 1;
        handle = GetStdHandle(STD_INPUT_HANDLE);
        pipe = !GetConsoleMode(handle, &dword);
        if (!pipe) {
            SetConsoleMode(handle, dword & ~(ENABLE_MOUSE_INPUT | ENABLE_WINDOW_INPUT));
            FlushConsoleInputBuffer(handle);
        }
    }
    if (pipe) {
        if (!PeekNamedPipe(handle, NULL, 0, NULL, &dword, NULL))
            return 1;
        return dword > 0;
    } else {
        GetNumberOfConsoleInputEvents(handle, &dword);
        return dword > 1;
    }
}

__forceinline void check(void) {
    char command[80];

    if (nodes & 4095 || rootDepth == 1) return;
    if (getInput()) {
        readLine(command, sizeof(command));
        if (strcmp(command, "stop") == 0) killSearch = 1;
        else if (strcmp(command, "ponderhit") == 0) pondering = 0;
    }
    if (!pondering && moveTime >= 0 && GetTickCount64() - startTime >= moveTime)
        killSearch = 1;
}

__forceinline D64 RX(void) {
    static D64 NXT = 1;
	return NXT = NXT * 1103515245 + 12345;
}

__forceinline void doMove(POST *position, int move, UNDO *undo) {
    int SIDE, fsq, tsq, ftp, TTP;

    SIDE = position->SIDE;
    fsq = move & 63;
    tsq = (move >> 6) & 63;
    ftp = TPONSQR(position, fsq);
    TTP = TPONSQR(position, tsq);
    undo->TTP = TTP;
    undo->CAPFLAGS = position->CAPFLAGS;
    undo->ENPSQR = position->ENPSQR;
    undo->REVMOVE = position->REVMOVE;
    undo->KEYLCT = position->KEYLCT;
    position->REPLIST[position->HEAD++] = position->KEYLCT;
    if (ftp == P || TTP != NOTP) position->REVMOVE = 0;
    else position->REVMOVE++;
    position->KEYLCT ^= zobristCastle[position->CAPFLAGS];
    position->CAPFLAGS &= captureMask[fsq] & captureMask[tsq];
    position->KEYLCT ^= zobristCastle[position->CAPFLAGS];
    if (position->ENPSQR != NOSQ) {
        position->KEYLCT ^= zobristEnPassant[FILE(position->ENPSQR)];
        position->ENPSQR = NOSQ;
    }
    position->PCC[fsq] = NOPC;
    position->PCC[tsq] = PC(SIDE, ftp);
    position->KEYLCT ^= zobristPC[PC(SIDE, ftp)][fsq] ^ zobristPC[PC(SIDE, ftp)][tsq];
    position->CLB[SIDE] ^= SQB(fsq) | SQB(tsq);
    position->TPB[ftp] ^= SQB(fsq) | SQB(tsq);
    position->PST[SIDE] += PST[ftp][tsq] - PST[ftp][fsq];
    if (ftp == K) position->KINGSQUARE[SIDE] = tsq;
    if (TTP != NOTP) {
        position->KEYLCT ^= zobristPC[PC(SIDE ^ 1, TTP)][tsq];
        position->CLB[SIDE ^ 1] ^= SQB(tsq);
        position->TPB[TTP] ^= SQB(tsq);
        position->MATERIAL[SIDE ^ 1] -= pieceValue[TTP];
        position->PST[SIDE ^ 1] -= PST[TTP][tsq];
    }
    switch (move >> 12) {
    case NORMAL: break;
    case CASTLE:
        if (tsq > fsq) {
            fsq += 3; --tsq;
        } else {
            fsq -= 4; ++tsq;
        }
        position->PCC[fsq] = NOPC;
        position->PCC[tsq] = PC(SIDE, R);
        position->KEYLCT ^= zobristPC[PC(SIDE, R)][fsq] ^ zobristPC[PC(SIDE, R)][tsq];
        position->CLB[SIDE] ^= SQB(fsq) | SQB(tsq);
        position->TPB[R] ^= SQB(fsq) | SQB(tsq);
        position->PST[SIDE] += PST[R][tsq] - PST[R][fsq];
        break;
    case EPCP:
        tsq ^= 8;
        position->PCC[tsq] = NOPC;
        position->KEYLCT ^= zobristPC[PC(SIDE ^ 1, P)][tsq];
        position->CLB[SIDE ^ 1] ^= SQB(tsq);
        position->TPB[P] ^= SQB(tsq);
        position->MATERIAL[SIDE ^ 1] -= pieceValue[P];
        position->PST[SIDE ^ 1] -= PST[P][tsq];
        break;
    case EPST:
        tsq ^= 8;
        if (pawnAttacks[SIDE][tsq] & PCB(position, SIDE ^ 1, P)) {
            position->ENPSQR = tsq;
            position->KEYLCT ^= zobristEnPassant[FILE(tsq)];
        }
        break;
    case PMN: case PMB: case PMR: case PMQ:
        ftp = (move >> 12) - 3;
        position->PCC[tsq] = PC(SIDE, ftp);
        position->KEYLCT ^= zobristPC[PC(SIDE, P)][tsq] ^ zobristPC[PC(SIDE, ftp)][tsq];
        position->TPB[P] ^= SQB(tsq);
        position->TPB[ftp] ^= SQB(tsq);
        position->MATERIAL[SIDE] += pieceValue[ftp] - pieceValue[P];
        position->PST[SIDE] += PST[ftp][tsq] - PST[P][tsq];
        break;
    }
    position->SIDE ^= 1;
    position->KEYLCT ^= ~(0ull);
}

__forceinline void undoMove(POST *position, int move, UNDO *undo) {
    int SIDE, fsq, tsq, ftp, TTP;

    SIDE = (position->SIDE) ^ 1;
    fsq = move & 63;
    tsq = (move >> 6) & 63;
    ftp = TPONSQR(position, tsq);
    TTP = undo->TTP;
    position->CAPFLAGS = undo->CAPFLAGS;
    position->ENPSQR = undo->ENPSQR;
    position->REVMOVE = undo->REVMOVE;
    position->KEYLCT = undo->KEYLCT;
    position->HEAD--;
    position->PCC[fsq] = PC(SIDE, ftp);
    position->PCC[tsq] = NOPC;
    position->CLB[SIDE] ^= SQB(fsq) | SQB(tsq);
    position->TPB[ftp] ^= SQB(fsq) | SQB(tsq);
    position->PST[SIDE] += PST[ftp][fsq] - PST[ftp][tsq];
    if (ftp == K) position->KINGSQUARE[SIDE] = fsq;
    if (TTP != NOTP) {
        position->PCC[tsq] = PC(SIDE ^ 1, TTP);
        position->CLB[SIDE ^ 1] ^= SQB(tsq);
        position->TPB[TTP] ^= SQB(tsq);
        position->MATERIAL[SIDE ^ 1] += pieceValue[TTP];
        position->PST[SIDE ^ 1] += PST[TTP][tsq];
    }
    switch (move >> 12) {
    case NORMAL: break;
    case CASTLE:
        if (tsq > fsq) {
            fsq += 3; --tsq;
        } else {
            fsq -= 4; ++tsq;
        }
        position->PCC[tsq] = NOPC;
        position->PCC[fsq] = PC(SIDE, R);
        position->CLB[SIDE] ^= SQB(fsq) | SQB(tsq);
        position->TPB[R] ^= SQB(fsq) | SQB(tsq);
        position->PST[SIDE] += PST[R][fsq] - PST[R][tsq];
        break;
    case EPCP:
        tsq ^= 8;
        position->PCC[tsq] = PC(SIDE ^ 1, P);
        position->CLB[SIDE ^ 1] ^= SQB(tsq);
        position->TPB[P] ^= SQB(tsq);
        position->MATERIAL[SIDE ^ 1] += pieceValue[P];
        position->PST[SIDE ^ 1] += PST[P][tsq];
        break;
    case EPST: break;
    case PMN: case PMB: case PMR: case PMQ:
        position->PCC[fsq] = PC(SIDE, P);
        position->TPB[P] ^= SQB(fsq);
        position->TPB[ftp] ^= SQB(fsq);
        position->MATERIAL[SIDE] += pieceValue[P] - pieceValue[ftp];
        position->PST[SIDE] += PST[P][fsq] - PST[ftp][fsq];
        break;
    }
    position->SIDE ^= 1;
}

int search(POST *position, int ply, int alpha, int beta, int depth, int *pv) {
    int best, score, move, newDepth, newPV[MPLY];
    MOVES moves[1]; UNDO undo[1];

    if (depth <= 0) return qSearch(position, ply, alpha, beta, pv); nodes++; check();
    if (killSearch) return 0;
    if (ply) *pv = 0;
    if (checkRepeat(position) && ply) return 0; move = 0;
    if (TTR(position->KEYLCT, &move, &score, alpha, beta, depth, ply)) return score;
    if (ply >= MPLY - 1) return evalPosition(position);
    if (depth > 1 && beta <= evalPosition(position) &&
		!(attacked(position, KINGSQR(position, position->SIDE), (position->SIDE) ^ 1)) &&
		((position->CLB[position->SIDE] & ~(position->TPB[P] | position->TPB[K])) != 0)) {
		undo->ENPSQR = position->ENPSQR;
		undo->KEYLCT = position->KEYLCT;
		position->REPLIST[position->HEAD++] = position->KEYLCT;
		position->REVMOVE++;
		if (position->ENPSQR != NOSQ) {
			position->KEYLCT ^= zobristEnPassant[FILE(position->ENPSQR)];
			position->ENPSQR = NOSQ;
		}
		position->SIDE ^= 1;
		position->KEYLCT ^= ~(0ull);
        score = -search(position, ply+1, -beta, -beta+1, depth-3, newPV);
		position->ENPSQR = undo->ENPSQR;
		position->KEYLCT = undo->KEYLCT;
		position->HEAD--;
		position->REVMOVE--;
		position->SIDE ^= 1;
        if (killSearch) return 0;
        if (score >= beta) {
            TTS(position->KEYLCT, 0, score, LOWER, depth, ply);
            return score;
        }
    }
    best = -INFINITY;
	moves->position = position;
    moves->PHASE = 0;
    moves->TTMOVE = move;
    moves->KM1 = killer[ply][0];
    moves->KM2 = killer[ply][1];
    while ((move = nextMove(moves))) {
        doMove(position, move, undo);
        if (attacked(position, KINGSQR(position, (position->SIDE) ^ 1), position->SIDE)) {
            undoMove(position, move, undo);
            continue;
        }
        newDepth = depth + attacked(position, KINGSQR(position, position->SIDE), (position->SIDE) ^ 1) - 1;
        if (best == -INFINITY) score = -search(position, ply+1, -beta, -alpha, newDepth, newPV);
        else {
            score = -search(position, ply+1, -alpha-1, -alpha, newDepth, newPV);
            if (!killSearch && score > alpha && score < beta)
                score = -search(position, ply+1, -beta, -alpha, newDepth, newPV);
        }
        undoMove(position, move, undo);
        if (killSearch) return 0;
        if (score >= beta) {
            TT(position, move, depth, ply);
            TTS(position->KEYLCT, move, score, LOWER, depth, ply);
            return score;
        }
        if (score > best) {
            best = score;
            if (score > alpha) {
                alpha = score;
				constructPV(pv, newPV, move);
				if (!ply) printPV(score, pv);
            }
        }
    }
    if (best == -INFINITY) {
		return attacked(position, KINGSQR(position, position->SIDE), (position->SIDE) ^ 1) ? -MATESCORE + ply : 0;
	}
    if (*pv) {
        TT(position, *pv, depth, ply);
		TTS(position->KEYLCT, *pv, best, EXACT, depth, ply);
    } else TTS(position->KEYLCT, 0, best, UPPER, depth, ply);
    return best;
}

int qSearch(POST *position, int ply, int alpha, int beta, int *pv) {
    int best, score, move, newPV[MPLY];
    MOVES moves[1]; UNDO undo[1];

    nodes++; check();
    if (killSearch) return 0; *pv = 0;
    if (checkRepeat(position)) return 0;
    if (ply >= MPLY - 1) return evalPosition(position); best = evalPosition(position);
    if (best >= beta) return best;
    if (best > alpha) alpha = best;
	moves->position = position;
    moves->LAST = genCaptures(moves->position, moves->move);
    scoreCaptures(moves);
    moves->NXT = moves->move;
    while ((move = nextCapture(moves))) {
        doMove(position, move, undo);
        if (attacked(position, KINGSQR(position, (position->SIDE) ^ 1), position->SIDE)) {
            undoMove(position, move, undo);
            continue;
        }
        score = -qSearch(position, ply+1, -beta, -alpha, newPV);
        undoMove(position, move, undo);
        if (killSearch) return 0;
        if (score >= beta) return score;
        if (score > best) {
            best = score;
            if (score > alpha) {
                alpha = score;
                constructPV(pv, newPV, move);
            }
        }
    }
    return best;
}

__forceinline int checkRepeat(POST *position) {
    int i;

    for (i = 4; i <= position->REVMOVE; i += 2)
        if (position->KEYLCT == position->REPLIST[position->HEAD-i])
            return 1;
    return 0;
}

int TTR(D64 KEYLCT, int *move, int *score, int alpha, int beta, int depth, int ply) {
    DATA *data;
    int i;

    data = transTable + (KEYLCT & transTableMask);
    for (i = 0; i < 4; i++, data++) {
        if (data->KEYLCT == KEYLCT) {
            data->DATE = transTableDate;
            *move = data->move;
            if (data->depth >= depth) {
                *score = data->score;
                if (*score < -MEVAL) *score += ply;
                else if (*score > MEVAL) *score -= ply;
                if ((data->FLAGS & UPPER && *score <= alpha) || (data->FLAGS & LOWER && *score >= beta))
                    return 1;
            }
            break;
        }
    }
    return 0;
}

void TTS(D64 KEYLCT, int move, int score, int FLAGS, int depth, int ply) {
    DATA *data, *replace;
    int i, oldest, age;

    if (score < -MEVAL) score -= ply;
    else if (score > MEVAL) score += ply;
    replace = NULL;
    oldest = -1;
    data = transTable + (KEYLCT & transTableMask);
    for (i = 0; i < 4; i++, data++) {
        if (data->KEYLCT == KEYLCT) {
            if (!move) move = data->move;
            replace = data;
            break;
        }
        age = (((transTableDate - data->DATE) & 255) << 8) + 255 - data->depth;
        if (age > oldest) {
            oldest = age;
            replace = data;
        }
    }
    replace->KEYLCT = KEYLCT; replace->DATE = transTableDate;
    replace->move = move;
	replace->score = score;
	replace->FLAGS = FLAGS;
	replace->depth = depth;
}

__forceinline int generateMob(POST *position, int SIDE) {
    D64 pieces;
    int mob = 0;

    for (pieces = PCB(position, SIDE, B); pieces; pieces &= pieces-1) {
        mob += POPCNT(BISHOPATT((position)->CLB[WC] | (position)->CLB[BC], BSF(pieces))) << 2;
    }
    for (pieces = PCB(position, SIDE, R); pieces; pieces &= pieces-1) {
        mob += POPCNT(ROOKATT((position)->CLB[WC] | (position)->CLB[BC], BSF(pieces))) << 2;
    }
    for (pieces = PCB(position, SIDE, Q); pieces; pieces &= pieces-1) {
        mob += POPCNT(QUEENATT((position)->CLB[WC] | (position)->CLB[BC], BSF(pieces))) << 1;
    }
    return mob;
}

__forceinline int evalPawnStruct(POST *position, int SIDE) {
    D64 pieces;
    int from, score = 0;

    for (pieces = PCB(position, SIDE, P); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        if (!(passedMask[SIDE][from] & PCB(position, SIDE ^ 1, P))) score += passedBonus[SIDE][RANK(from)];
        if (!(adjacentMask[FILE(from)] & PCB(position, SIDE, P))) score -= 16;
    }
    return score;
}

__forceinline int evalKingSafety(POST *position, int SIDE) {
    if (!PCB(position, SIDE ^ 1, Q) || position->MATERIAL[SIDE ^ 1] <= 1650) return 0;
    return (-2) * PST[K][KINGSQR(position, SIDE)];
}

__forceinline int evalPosition(POST *position) {
    int score;

    score = position->MATERIAL[WC] - position->MATERIAL[BC];
    if (score < 300 && score > -300) score += generateMob(position, WC) - generateMob(position, BC);
    score += position->PST[WC] - position->PST[BC];
    score += evalPawnStruct(position, WC) - evalPawnStruct(position, BC);
    score += evalKingSafety(position, WC) - evalKingSafety(position, BC);
    if (score < -MEVAL) score = -MEVAL;
    else if (score > MEVAL) score = MEVAL;
    return position->SIDE == WC ? score : -score;
}

__forceinline int *genCaptures(POST *position, int *list) {
    D64 pieces, moves;
    int SIDE, from, to;

    if ((SIDE = position->SIDE) == WC) {
        moves = ((PCB(position, WC, P) & ~0x0101010101010101ull & 0x00FF000000000000ull) << 7) & position->CLB[BC];
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to - 7);
            *list++ = (PMR << 12) | (to << 6) | (to - 7);
            *list++ = (PMB << 12) | (to << 6) | (to - 7);
            *list++ = (PMN << 12) | (to << 6) | (to - 7);
            moves &= moves-1;
        }
        moves = ((PCB(position, WC, P) & ~0x8080808080808080ull & 0x00FF000000000000ull) << 9) & position->CLB[BC];
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to - 9);
            *list++ = (PMR << 12) | (to << 6) | (to - 9);
            *list++ = (PMB << 12) | (to << 6) | (to - 9);
            *list++ = (PMN << 12) | (to << 6) | (to - 9);
            moves &= moves-1;
        }
        moves = ((PCB(position, WC, P) & 0x00FF000000000000ull) << 8) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to - 8);
            *list++ = (PMR << 12) | (to << 6) | (to - 8);
            *list++ = (PMB << 12) | (to << 6) | (to - 8);
            *list++ = (PMN << 12) | (to << 6) | (to - 8);
            moves &= moves-1;
        }
        moves = ((PCB(position, WC, P) & ~0x0101010101010101ull & ~0x00FF000000000000ull) << 7) & position->CLB[BC];
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to - 7);
            moves &= moves-1;
        }
        moves = ((PCB(position, WC, P) & ~0x8080808080808080ull & ~0x00FF000000000000ull) << 9) & position->CLB[BC];
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to - 9);
            moves &= moves-1;
        }
        if ((to = position->ENPSQR) != NOSQ) {
            if (((PCB(position, WC, P) & ~0x0101010101010101ull) << 7) & SQB(to))
                *list++ = (EPCP << 12) | (to << 6) | (to - 7);
            if (((PCB(position, WC, P) & ~0x8080808080808080ull) << 9) & SQB(to))
                *list++ = (EPCP << 12) | (to << 6) | (to - 9);
        }
    } else {
        moves = ((PCB(position, BC, P) & ~0x0101010101010101ull & 0x000000000000FF00ull) >> 9) & position->CLB[WC];
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to + 9);
            *list++ = (PMR << 12) | (to << 6) | (to + 9);
            *list++ = (PMB << 12) | (to << 6) | (to + 9);
            *list++ = (PMN << 12) | (to << 6) | (to + 9);
            moves &= moves-1;
        }
        moves = ((PCB(position, BC, P) & ~0x8080808080808080ull & 0x000000000000FF00ull) >> 7) & position->CLB[WC];
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to + 7);
            *list++ = (PMR << 12) | (to << 6) | (to + 7);
            *list++ = (PMB << 12) | (to << 6) | (to + 7);
            *list++ = (PMN << 12) | (to << 6) | (to + 7);
            moves &= moves-1;
        }
        moves = ((PCB(position, BC, P) & 0x000000000000FF00ull) >> 8) & (~((position)->CLB[WC] | (position)->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (PMQ << 12) | (to << 6) | (to + 8);
            *list++ = (PMR << 12) | (to << 6) | (to + 8);
            *list++ = (PMB << 12) | (to << 6) | (to + 8);
            *list++ = (PMN << 12) | (to << 6) | (to + 8);
            moves &= moves-1;
        }
        moves = ((PCB(position, BC, P) & ~0x0101010101010101ull & ~0x000000000000FF00ull) >> 9) & position->CLB[WC];
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to + 9);
            moves &= moves-1;
        }
        moves = ((PCB(position, BC, P) & ~0x8080808080808080ull & ~0x000000000000FF00ull) >> 7) & position->CLB[WC];
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to + 7);
            moves &= moves-1;
        }
        if ((to = position->ENPSQR) != NOSQ) {
            if (((PCB(position, BC, P) & ~0x0101010101010101ull) >> 9) & SQB(to))
                *list++ = (EPCP << 12) | (to << 6) | (to + 9);
            if (((PCB(position, BC, P) & ~0x8080808080808080ull) >> 7) & SQB(to))
                *list++ = (EPCP << 12) | (to << 6) | (to + 7);
        }
    }
	for (pieces = PCB(position, SIDE, N); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = knightAttacks[from] & position->CLB[SIDE ^ 1];
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves-1;
        }
    }
    for (pieces = PCB(position, SIDE, B); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = BISHOPATT(position->CLB[WC] | position->CLB[BC], from) & position->CLB[SIDE ^ 1];
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves-1;
        }
    }
    for (pieces = PCB(position, SIDE, R); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = ROOKATT(position->CLB[WC] | position->CLB[BC], from) & position->CLB[SIDE ^ 1];
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves-1;
        }
    }
	for (pieces = PCB(position, SIDE, Q); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = QUEENATT(position->CLB[WC] | position->CLB[BC], from) & position->CLB[SIDE ^ 1];
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves-1;
        }
    }
    moves = kingAttacks[KINGSQR(position, SIDE)] & position->CLB[SIDE ^ 1];
    while (moves) {
        *list++ = (BSF(moves) << 6) | KINGSQR(position, SIDE);
        moves &= moves-1;
    }
    return list;
}

static int ISLEGAL(POST *position, int move) {
    int SIDE, fsq, tsq, ftp, TTP;
	D64 result = 0;

    SIDE = position->SIDE;
    fsq = move & 63;
    tsq = (move >> 6) & 63;
    ftp = TPONSQR(position, fsq);
    TTP = TPONSQR(position, tsq);
    if (ftp == NOTP || (position->PCC[fsq] & 1) != SIDE) return 0;
    if (TTP != NOTP && (position->PCC[tsq] & 1) == SIDE) return 0;
    switch (move >> 12) {
    case NORMAL: break;
    case CASTLE:
        if (SIDE == WC) {
            if (fsq != E1) return 0;
            if (tsq > fsq) {
                if ((position->CAPFLAGS & 1) && !((position->CLB[WC] | position->CLB[BC]) & 0x0000000000000060ull))
                    if (!attacked(position, E1, BC) && !attacked(position, F1, BC)) return 1;
            } else {
                if ((position->CAPFLAGS & 2) && !((position->CLB[WC] | position->CLB[BC]) & 0x000000000000000Eull))
                    if (!attacked(position, E1, BC) && !attacked(position, D1, BC)) return 1;
            }
        } else {
            if (fsq != E8) return 0;
            if (tsq > fsq) {
                if ((position->CAPFLAGS & 4) && !((position->CLB[WC] | position->CLB[BC]) & 0x6000000000000000ull))
                    if (!attacked(position, E8, WC) && !attacked(position, F8, WC)) return 1;
            } else {
                if ((position->CAPFLAGS & 8) && !((position->CLB[WC] | position->CLB[BC]) & 0x0E00000000000000ull))
                    if (!attacked(position, E8, WC) && !attacked(position, D8, WC)) return 1;
            }
        }
        return 0;
    case EPCP:
        if (ftp == P && tsq == position->ENPSQR) return 1;
        return 0;
    case EPST:
        if (ftp == P && TTP == NOTP && position->PCC[tsq ^ 8] == NOPC)
            if ((tsq > fsq && SIDE == WC) || (tsq < fsq && SIDE == BC)) return 1;
        return 0;
    }
    if (ftp == P) {
        if (SIDE == WC) {
            if (RANK(fsq) == R7 && !(move & 0x4000)) return 0;
            if (tsq - fsq == 8)
                if (TTP == NOTP) return 1;
            if ((tsq - fsq == 7 && FILE(fsq) != FA) || (tsq - fsq == 9 && FILE(fsq) != FH))
                if (TTP != NOTP) return 1;
        } else {
            if (RANK(fsq) == R2 && !(move & 0x4000)) return 0;
            if (tsq - fsq == -8)
                if (TTP == NOTP) return 1;
            if ((tsq - fsq == -9 && FILE(fsq) != FA) || (tsq - fsq == -7 && FILE(fsq) != FH))
                if (TTP != NOTP) return 1;
        }
        return 0;
    }
    if (move & 0x4000) return 0;
	switch (TPONSQR(position, fsq)) {
		case P: result = pawnAttacks[position->PCC[fsq] & 1][fsq]; break;
		case N: result = knightAttacks[fsq]; break;
		case B: result = BISHOPATT(position->CLB[WC] | position->CLB[BC], fsq); break;
		case R: result = ROOKATT(position->CLB[WC] | position->CLB[BC], fsq); break;
		case Q: result = QUEENATT(position->CLB[WC] | position->CLB[BC], fsq); break;
		case K: result = kingAttacks[fsq]; break;
    }
    return (result & SQB(tsq)) != 0;
}

int *genQuietPOS(POST *position, int *list) {
    D64 pieces, moves;
    int SIDE, from, to;

    SIDE = position->SIDE;
    if (SIDE == WC) {
        if ((position->CAPFLAGS & 1) && !((position->CLB[WC] | position->CLB[BC]) & 0x0000000000000060ull))
            if (!attacked(position, E1, BC) && !attacked(position, F1, BC)) *list++ = (CASTLE << 12) | (G1 << 6) | E1;
        if ((position->CAPFLAGS & 2) && !((position->CLB[WC] | position->CLB[BC]) & 0x000000000000000Eull))
            if (!attacked(position, E1, BC) && !attacked(position, D1, BC)) *list++ = (CASTLE << 12) | (C1 << 6) | E1;
        moves = ((((PCB(position, WC, P) & 0x000000000000FF00ull) << 8) & (~(position->CLB[WC] | position->CLB[BC]))) << 8) &
			(~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (EPST << 12) | (to << 6) | (to - 16);
            moves &= moves - 1;
        }
        moves = ((PCB(position, WC, P) & ~0x00FF000000000000ull) << 8) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to - 8);
            moves &= moves - 1;
        }
    } else {
        if ((position->CAPFLAGS & 4) && !((position->CLB[WC] | position->CLB[BC]) & 0x6000000000000000ull))
            if (!attacked(position, E8, WC) && !attacked(position, F8, WC)) *list++ = (CASTLE << 12) | (G8 << 6) | E8;
        if ((position->CAPFLAGS & 8) && !((position->CLB[WC] | position->CLB[BC]) & 0x0E00000000000000ull))
            if (!attacked(position, E8, WC) && !attacked(position, D8, WC)) *list++ = (CASTLE << 12) | (C8 << 6) | E8;
        moves = ((((PCB(position, BC, P) & 0x00FF000000000000ull) >> 8) & (~(position->CLB[WC] | position->CLB[BC]))) >> 8) &
			(~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (EPST << 12) | (to << 6) | (to + 16);
            moves &= moves - 1;
        }
        moves = ((PCB(position, BC, P) & ~0x000000000000FF00ull) >> 8) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            to = BSF(moves);
            *list++ = (to << 6) | (to + 8);
            moves &= moves - 1;
        }
    }
    for (pieces = PCB(position, SIDE, N); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = knightAttacks[from] & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves - 1;
        }
    }
	for (pieces = PCB(position, SIDE, B); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = BISHOPATT(position->CLB[WC] | position->CLB[BC], from) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves - 1;
        }
    }
    for (pieces = PCB(position, SIDE, R); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = ROOKATT(position->CLB[WC] | position->CLB[BC], from) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves - 1;
        }
    }
    for (pieces = PCB(position, SIDE, Q); pieces; pieces &= pieces-1) {
        from = BSF(pieces);
        moves = QUEENATT(position->CLB[WC] | position->CLB[BC], from) & (~(position->CLB[WC] | position->CLB[BC]));
        while (moves) {
            *list++ = (BSF(moves) << 6) | from;
            moves &= moves - 1;
        }
    }
    moves = kingAttacks[KINGSQR(position, SIDE)] & (~(position->CLB[WC] | position->CLB[BC]));
    while (moves) {
        *list++ = (BSF(moves) << 6) | KINGSQR(position, SIDE);
        moves &= moves - 1;
    }
    return list;
}

__forceinline int nextMove(MOVES *moves) {
    int move;

    switch (moves->PHASE) {
    case 0:
        move = moves->TTMOVE;
        if (move && ISLEGAL(moves->position, move)) {
            moves->PHASE = 1;
            return move;
        }
    case 1:
        moves->LAST = genCaptures(moves->position, moves->move);
        scoreCaptures(moves);
        moves->NXT = moves->move;
        moves->BADPWN = moves->BAD;
        moves->PHASE = 2;
    case 2:
        while (moves->NXT < moves->LAST) {
            move = sortBest(moves);
            if (move == moves->TTMOVE) continue;
            if (poorCapture(moves->position, move)) {
                *moves->BADPWN++ = move;
                continue;
            }
            return move;
        }
    case 3:
        move = moves->KM1;
        if (move && move != moves->TTMOVE && moves->position->PCC[(move >> 6) & 63] == NOPC &&
			ISLEGAL(moves->position, move)) {
            moves->PHASE = 4;
            return move;
        }
    case 4:
        move = moves->KM2;
        if (move && move != moves->TTMOVE && moves->position->PCC[(move >> 6) & 63] == NOPC &&
			ISLEGAL(moves->position, move)) {
            moves->PHASE = 5;
            return move;
        }
    case 5:
        moves->LAST = genQuietPOS(moves->position, moves->move);
        scoreQuietPOS(moves);
        moves->NXT = moves->move;
        moves->PHASE = 6;
    case 6:
        while (moves->NXT < moves->LAST) {
            move = sortBest(moves);
            if (move == moves->TTMOVE || move == moves->KM1 || move == moves->KM2) continue;
            return move;
        }
        moves->NXT = moves->BAD;
        moves->PHASE = 7;
    case 7:
        if (moves->NXT < moves->BADPWN) return *moves->NXT++;
    }
    return 0;
}

__forceinline void printPV(int score, int *pv) {
	long time;
    char *type, pvStr[256];

    type = "mate";
    if (score < -MEVAL) score = (-MATESCORE - score) >> 1;
    else if (score > MEVAL) score = (MATESCORE - score + 1) >> 1;
    else type = "cp";
    convertPV(pv, pvStr);
	time = GetTickCount64() - startTime;
    printf("info depth %d time %d nodes %d nps %d score %s %d pv %s\n",
		rootDepth, time, nodes, nodes/(time+1)*1000, type, score, pvStr);
}

__forceinline int nextCapture(MOVES *moves) {
    int move;

    while (moves->NXT < moves->LAST) {
        move = sortBest(moves);
        if (poorCapture(moves->position, move)) continue;
        return move;
    }
    return 0;
}

__forceinline void scoreCaptures(MOVES *moves) {
    int *movep, *valuep;

    valuep = moves->value;
    for (movep = moves->move; movep < moves->LAST; movep++)
        *valuep++ = mvvlva(moves->position, *movep);
}

__forceinline void scoreQuietPOS(MOVES *moves) {
    int *movep, *valuep;

    valuep = moves->value;
    for (movep = moves->move; movep < moves->LAST; movep++)
        *valuep++ = history[moves->position->PCC[*movep & 63]][(*movep >> 6) & 63];
}

__forceinline int sortBest(MOVES *moves) {
    int *movep, *valuep, aux;

    valuep = moves->value + (moves->LAST - moves->move)-1;
    for (movep = moves->LAST-1; movep > moves->NXT; movep--, valuep--) {
        if (*valuep > *(valuep-1)) {
            aux = *valuep; *valuep = *(valuep-1); *(valuep-1) = aux;
            aux = *movep; *movep = *(movep-1); *(movep-1) = aux;
        }
    }
    return *moves->NXT++;
}

__forceinline int poorCapture(POST *position, int move) {
	D64 attackers, occ, typeX;
    int fsq, tsq, SIDE, ply, type, score[32];

    fsq = move & 63;
    tsq = (move >> 6) & 63;
    if (pieceValue[TPONSQR(position, tsq)] >= pieceValue[TPONSQR(position, fsq)]) return 0;
    if ((move >> 12) == EPCP) return 0;
    attackers = (PCB(position, WC, P) & pawnAttacks[BC][tsq]) | (PCB(position, BC, P) & pawnAttacks[WC][tsq]) |
		(position->TPB[N] & knightAttacks[tsq]) | ((position->TPB[B] | position->TPB[Q]) &
		BISHOPATT((position)->CLB[WC] | (position)->CLB[BC], tsq)) | ((position->TPB[R] | position->TPB[Q]) &
		ROOKATT((position)->CLB[WC] | (position)->CLB[BC], tsq)) | (position->TPB[K] & kingAttacks[tsq]);
    occ = (position)->CLB[WC] | (position)->CLB[BC];
    score[0] = pieceValue[TPONSQR(position, tsq)];
    type = TPONSQR(position, fsq);
    occ ^= 1ull << fsq;
    attackers |= (BISHOPATT(occ, tsq) & (position->TPB[B] | position->TPB[Q])) |
		(ROOKATT(occ, tsq) & (position->TPB[R] | position->TPB[Q]));
    attackers &= occ;
    SIDE = (position->SIDE) ^ 1;
    for (ply = 1; attackers & position->CLB[SIDE]; ply++) {
        if (type == K) {
            score[ply++] = INFINITY;
            break;
        }
        score[ply] = -score[ply-1] + pieceValue[type];
        for (type = P; type <= K; type++)
            if ((typeX = PCB(position, SIDE, type) & attackers)) break;
        occ ^= typeX & -typeX;
        attackers |= (BISHOPATT(occ, tsq) & (position->TPB[B] | position->TPB[Q])) |
			(ROOKATT(occ, tsq) & (position->TPB[R] | position->TPB[Q]));
        attackers &= occ;
        SIDE ^= 1;
    }
    for (; --ply; score[ply-1] = -max(-score[ply-1], score[ply]));
    return score[0] < 0;
}

__forceinline int mvvlva(POST *position, int move) {
    if (position->PCC[(move >> 6) & 63] != NOPC)
		return TPONSQR(position, (move >> 6) & 63) * 6 + 5 - TPONSQR(position, move & 63);
    if (move & 0x4000) return (move >> 12) - 8;
    return 5;
}

__forceinline void TT(POST *position, int move, int depth, int ply) {
    if (position->PCC[(move >> 6) & 63] != NOPC || (move & 0x4000) || (move >> 12) == EPCP) return;
    history[position->PCC[move & 63]][(move >> 6) & 63] += depth;
    if (move != killer[ply][0]) {
        killer[ply][1] = killer[ply][0];
        killer[ply][0] = move;
    }
}

__forceinline void convertStr(int move, char *moveStr) {
    static const char promotionChar[5] = "nbrq";

    moveStr[0] = FILE(move & 63) + 'a';
    moveStr[1] = RANK(move & 63) + '1';
    moveStr[2] = FILE((move >> 6) & 63) + 'a';
    moveStr[3] = RANK((move >> 6) & 63) + '1';
    moveStr[4] = '\0';
    if (move & 0x4000) {
        moveStr[4] = promotionChar[(move >> 12) & 3];
        moveStr[5] = '\0';
    }
}

__forceinline void convertPV(int *pv, char *pvStr) {
    int *movep;
    char moveStr[6];

    pvStr[0] = '\0';
    for (movep = pv; *movep; movep++) {
        convertStr(*movep, moveStr);
        strcat(pvStr, moveStr);
        strcat(pvStr, " ");
    }
}

__forceinline void constructPV(int *dst, int *src, int move) {
    *dst++ = move;
	while ((*dst++ = *src++));
}

__forceinline int attacked(POST *position, int sq, int SIDE) {
    return (PCB(position, SIDE, P) & pawnAttacks[SIDE ^ 1][sq]) || (PCB(position, SIDE, N) & knightAttacks[sq]) ||
           ((PCB(position, SIDE, B) | PCB(position, SIDE, Q)) & BISHOPATT(position->CLB[WC] | position->CLB[BC], sq)) ||
           ((PCB(position, SIDE, R) | PCB(position, SIDE, Q)) & ROOKATT(position->CLB[WC] | position->CLB[BC], sq)) ||
           (PCB(position, SIDE, K) & kingAttacks[sq]);
}

/*  SEARCH END  */

int main() {
    printf(INFO_STRING NAME " " BUILD_BRANCH " build number " BUILD_NUMBER ", " BUILD_PROT);
	printf("\n"INFO_STRING NAME " built on " __TIMESTAMP__ "\n");
	fflush(stdout);
    buildTable();
    uciControl();
    return 0;
}
