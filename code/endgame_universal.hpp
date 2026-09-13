#pragma once
#include "board_inc.hpp"
#include <cstdint>
#include <stdexcept>

// Exact WDL for every legal nonterminal gravity board with <= 12 empty cells.
// No shape/threat gate; solve_tree also works beyond that range without memo.
// init_lines() and init_sq_lines() must have been called, as for BoardInc.
// Carries all current threats; only lines through the new stone can add threats.
// Score is WDL, not distance to mate. Caller handles already finished games.
namespace endgame_universal {
using U64 = unsigned long long;
struct Stats { unsigned long long nodes = 0, line_updates = 0, removed_moves = 0, memo_hits = 0; };

struct Entry { uint32_t generation = 0; int8_t lower = -1, upper = 1; };
struct Workspace {
    std::vector<Entry> entries;
    uint32_t generation = 0;
    int power[64] = {}, initial_empty = 0;
    void begin(U64 free) {
        initial_empty = __builtin_popcountll(free);
        if (initial_empty > 12) throw std::invalid_argument("universal memo solver requires E <= 12");
        int size = 1;
        while (free) {
            const U64 bit = free & -free; free ^= bit;
            power[__builtin_ctzll(bit)] = size;
            size *= 3;
        }
        if (entries.size() < (size_t)size) entries.resize(size);
        if (++generation == 0) {
            for (auto& entry : entries) entry.generation = 0;
            generation = 1;
        }
    }
};

template<bool Count, bool Memo = false>
inline int visit(U64 me, U64 you, U64 hand, U64 rm, U64 ry,
                 int empty, int alpha, int beta, Stats* stats, Workspace* workspace = nullptr, int code = 0)
{
    if constexpr (Count) ++stats->nodes;
#ifdef ENDGAME_UNIVERSAL_VERIFY
    const U64 free_check = ~(me | you);
    if (rm != (Board::reach(me) & free_check) || ry != (Board::reach(you) & free_check) ||
        hand != (((me | you) << 16 | 0xffffULL) & free_check)) std::abort();
#endif
    if (!hand) return 0;
    if (hand & rm) return 1;
    U64 choices = hand;
    const U64 forced = hand & ry;
    if (forced) {
        if (forced & (forced-1)) return -1;
        choices = forced;
    }
    // Opening an opponent threat immediately above loses on the next move.
    choices &= ~(ry >> 16);
    if constexpr (Count) stats->removed_moves += __builtin_popcountll(hand ^ choices);
    if (!choices) return -1;
    // At most two cells: a safe nonwinning first move leaves no winning reply.
    if (empty <= 2) return 0;
    Entry* entry = nullptr;
    if constexpr (Memo) {
        entry = &workspace->entries[code];
        if (entry->generation != workspace->generation) {
            entry->generation = workspace->generation;
            entry->lower = -1; entry->upper = 1;
        } else {
            if (entry->lower == entry->upper || entry->lower >= beta) {
                if constexpr (Count) ++stats->memo_hits;
                return entry->lower;
            }
            if (entry->upper <= alpha) {
                if constexpr (Count) ++stats->memo_hits;
                return entry->upper;
            }
            alpha = std::max(alpha,(int)entry->lower);
            beta = std::min(beta,(int)entry->upper);
        }
    }
    const int original_alpha = alpha, original_beta = beta;
    int best = -1;
    while (choices) {
        const U64 bit = choices & -choices;
        choices ^= bit;
        const U64 next_me = me | bit;
        const U64 free = ~(next_me | you);
        const U64 next_hand = (hand ^ bit) | ((bit << 16) & free);
        U64 next_rm = rm & free;
        // Existing threats persist except at the occupied cell. Newly created
        // threats can only belong to the mover and to one of these 4--7 lines.
        for (const unsigned char* p = SQ_LINES[__builtin_ctzll(bit)]; *p != 0xFF; ++p) {
            if constexpr (Count) ++stats->line_updates;
            const U64 rest = LINES[*p] & ~next_me;
            if (!(rest & (rest-1))) next_rm |= rest & free;
        }
        int child_code = 0;
        if constexpr (Memo) child_code = code + (1+(workspace->initial_empty-empty)%2)*workspace->power[__builtin_ctzll(bit)];
        const int value = -visit<Count,Memo>(you, next_me, next_hand, ry & free, next_rm,
                                        empty-1, -beta, -alpha, stats, workspace, child_code);
        if (value > best) best = value;
        if (best > alpha) alpha = best;
        if (alpha >= beta) break;
    }
    if constexpr (Memo) {
        if (best <= original_alpha) entry->upper = std::min((int)entry->upper,best);
        else if (best >= original_beta) entry->lower = std::max((int)entry->lower,best);
        else entry->lower = entry->upper = best;
    }
    return best;
}

template<bool Count = false>
inline int solve_tree(const Board& b, Stats* stats = nullptr)
{
    const U64 hand = b.valid_move();
    if (!hand) return 0;
    const U64 rm = Board::reach(b.Me);
    // Preserve the existing engine's inexpensive immediate-win exit.
    if (hand & rm) {
        if constexpr (Count) ++stats->nodes;
        return 1;
    }
    const U64 free = ~(b.Me | b.You);
    return visit<Count>(b.Me, b.You, hand, rm & free, Board::reach(b.You) & free,
                        __builtin_popcountll(free), -1, 1, stats);
}

// A fresh generation isolates each root without clearing the whole ternary table.
// The direct ternary address has no hash collision. Bounds are kept separately.
// Short tails use the same universal recurrence without memo bookkeeping.
template<bool Count = false>
inline int solve(const Board& b, Stats* stats = nullptr)
{
    const U64 hand = b.valid_move();
    if (!hand) return 0;
    const U64 free = ~(b.Me | b.You);
    const int empty = __builtin_popcountll(free);
    if (empty <= 5) return solve_tree<Count>(b, stats);
    const U64 rm = Board::reach(b.Me);
    if (hand & rm) {
        if constexpr (Count) ++stats->nodes;
        return 1;
    }
    static thread_local Workspace workspace;
    workspace.begin(free);
    return visit<Count,true>(b.Me, b.You, hand, rm & free, Board::reach(b.You) & free,
                            empty, -1, 1, stats, &workspace);
}
} // namespace endgame_universal
