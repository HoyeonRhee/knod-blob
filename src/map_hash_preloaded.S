#if KNOD_ISA == 10 || KNOD_ISA == 11
// SPDX-License-Identifier: GPL-2.0-or-later
//
// Hash map lookup.
//
// One routine per key length, because the key is copied, hashed and compared a
// dword at a time and the length decides how many times.  The JIT knows the
// length when it splices, so it picks the routine rather than the routine
// looping over a runtime count.

#include "common.inc"
#include "jhash.inc"

// A lookup is given no value, so it spends the value registers on holding the
// stored key whole and comparing it a word at a time against the search key.
// That is what sets the 56-byte key limit, not any property of hashing.
#define K0		KEY			// v28-v41
#define M0		VAL			// v42-v55

// jhash state and its scratch borrow the stored-key registers, which are not
// written until the walk starts and the hash is finished before then.
#define HA		(M0 + 0)
#define HB		(M0 + 1)
#define HC		(M0 + 2)
#define HT		(M0 + 3)

#define EBASE		T0		// element storage base
#define EADDR		T2		// the element being examined
#define NEND		THI0
#define CHAIN		THI1

#define KNOD_BPF_HASH_NEXT_END		0x7FFFFFFF
#define KNOD_BPF_HASH_NEXT_MASK		0x7FFFFFFF
#define ELEM_OFF_NEXT			0
#define ELEM_OFF_KV			KNOD_BLOB_ELEM_KV_OFF

	.text

//
// knod_lookup_hash_preloaded_k<n>
//
//   r0 = the value belonging to the key, or 0
//
// The chain is walked with the lanes still resident: a lane whose chain ends
// is removed from EXEC rather than branched away, so lanes at different depths
// share the walk and the loop runs as long as any lane is still looking.  The
// mask is put back at the end and the lanes that dropped out keep the zero
// written up front, which is what a miss looks like.
//
.macro	DEFINE_LOOKUP_HASH_PRELOADED n
	.globl knod_lookup_hash_preloaded_k\n
	.p2align 2
knod_lookup_hash_preloaded_k\n:
	// Caller supplied immutable descriptor facts after staging the key.
	v_mov_b32 v[RET], 0
	v_mov_b32 v[RET+1], 0

	JHASH HA, HB, HC, HT, K0, \n, S0

	// bucket_id = hash & (n_buckets - 1)
	v_and_b32 v[HC], s[S3], v[HC]
	// The bucket mask is dead; retain the caller-supplied immutable stride.
	s_mov_b32 s[S3], s[KNOD_BLOB_HASH_PRE_STRIDE_SREG]

	// &bucket[bucket_id].  s[S0:S0+1] is only the carry out; the bucket
	// base it held is in v[NEND:CHAIN], which the mad may not write over.
	v_mad_u64_u32 v[EADDR:EADDR+1], s[S0:S0+1], 4, v[HC], v[NEND:CHAIN]

	// Every lane starts the walk; the mask comes back at .Lpreloaded_out.
	s_mov_b64 s[XSAVE0:XSAVE0+1], exec
	v_mov_b32 v[NEND], KNOD_BPF_HASH_NEXT_END

.Lpreloaded_next\n:
	global_load_dword v[CHAIN], v[EADDR:EADDR+1], off MAP_COHERENT
	// The caller supplied all descriptor facts; only the chain read is pending.
	s_waitcnt vmcnt(0)
	// The top bit marks a deleted element; it is not part of the index.
	v_and_b32 v[CHAIN], KNOD_BPF_HASH_NEXT_MASK, v[CHAIN]

	// Lanes that reached the end of their chain stop here.
	v_cmp_eq_u32 vcc, v[NEND], v[CHAIN]
	s_andn2_b64 exec, exec, vcc
	s_cbranch_execz .Lpreloaded_out\n

	// elem = elems + elem_id * elem_size
	v_mad_u64_u32 v[EADDR:EADDR+1], s[S0:S0+1], s[S3], v[CHAIN], v[EBASE:EBASE+1]
	// A concurrent delete can mark an element already reached by this
	// walk.  Its next field carries the deletion mark, just as in the JIT.
	global_load_dword v[CHAIN], v[EADDR:EADDR+1], off MAP_COHERENT

	// Exact rounded-key bytes; M0..M0+n-1 are contiguous and private
	// temporaries. Keep the coherent next/deletion read above unchanged.
	.set _i, 0
	.rept (\n / 4)
	global_load_dwordx4 v[M0 + _i:M0 + _i + 3], v[EADDR:EADDR+1], off offset:(ELEM_OFF_KV + _i * 4) MAP_COHERENT
	.set _i, _i + 4
	.endr
	.if ((\n % 4) >= 2)
	global_load_dwordx2 v[M0 + _i:M0 + _i + 1], v[EADDR:EADDR+1], off offset:(ELEM_OFF_KV + _i * 4) MAP_COHERENT
	.set _i, _i + 2
	.endif
	.if (\n % 2)
	global_load_dword v[M0 + _i], v[EADDR:EADDR+1], off offset:(ELEM_OFF_KV + _i * 4) MAP_COHERENT
	.endif
	s_waitcnt vmcnt(0)

	// Fold the per-dword comparisons into one mask rather than branching
	// on each: the padding is zero on both sides, so the last dword
	// compares equal without masking.
	v_cmp_eq_u32 vcc, v[K0], v[M0]
	s_and_b64 s[XSAVE1:XSAVE1+1], exec, vcc
	.set _i, 1
	.rept (\n - 1)
	v_cmp_eq_u32 vcc, v[K0 + _i], v[M0 + _i]
	s_and_b64 s[XSAVE1:XSAVE1+1], s[XSAVE1:XSAVE1+1], vcc
	.set _i, _i + 1
	.endr

	// Bit 31 marks a deleted element.  Keep walking through it instead of
	// returning its value, even when the key compares equal.
	v_cmp_le_i32 vcc, 0, v[CHAIN]
	s_and_b64 s[XSAVE1:XSAVE1+1], s[XSAVE1:XSAVE1+1], vcc

	// Matching lanes take the value and leave the walk.
	s_and_saveexec_b64 s[XSAVE2:XSAVE2+1], s[XSAVE1:XSAVE1+1]
	s_cbranch_execz .Lpreloaded_miss\n
	v_add_co_u32 v[RET], vcc, KNOD_BLOB_ELEM_VALUE_OFF(\n), v[EADDR]
	V_ADD_CI_U32 v[RET+1], vcc, 0, v[EADDR+1], vcc
.Lpreloaded_miss\n:
	// exec = lanes still walking = (those that were walking) - (matched)
	s_andn2_b64 exec, s[XSAVE2:XSAVE2+1], s[XSAVE1:XSAVE1+1]
	s_cbranch_execz .Lpreloaded_out\n

	// Follow the chain.  v[EADDR:EADDR+1] already points at the element
	// and its next index sits at offset zero, which is what .Lpreloaded_next reloads.
	s_branch .Lpreloaded_next\n

.Lpreloaded_out\n:
	s_mov_b64 exec, s[XSAVE0:XSAVE0+1]
	KNOD_BLOB_RET
	.size knod_lookup_hash_preloaded_k\n, . - knod_lookup_hash_preloaded_k\n

	.globl knod_lookup_hash_preloaded_k\n\()_xsave
	.set knod_lookup_hash_preloaded_k\n\()_xsave, 3
.endm

// One per DIV_ROUND_UP(key_size, 4) the JIT will accept.  Spelled out rather
// than generated, because the length is pasted into label names as well as
// counted with, and only a literal does both.
	DEFINE_LOOKUP_HASH_PRELOADED 1
	DEFINE_LOOKUP_HASH_PRELOADED 2
	DEFINE_LOOKUP_HASH_PRELOADED 3
	DEFINE_LOOKUP_HASH_PRELOADED 4
	DEFINE_LOOKUP_HASH_PRELOADED 5
	DEFINE_LOOKUP_HASH_PRELOADED 6
	DEFINE_LOOKUP_HASH_PRELOADED 7
	DEFINE_LOOKUP_HASH_PRELOADED 8
	DEFINE_LOOKUP_HASH_PRELOADED 9
	DEFINE_LOOKUP_HASH_PRELOADED 10
	DEFINE_LOOKUP_HASH_PRELOADED 11
	DEFINE_LOOKUP_HASH_PRELOADED 12
	DEFINE_LOOKUP_HASH_PRELOADED 13
	DEFINE_LOOKUP_HASH_PRELOADED 14

// The build concatenates every source into one file, so these names are
// shared with whatever follows.  Handing them back keeps the next file's
// meaning its own, and keeps a collision an error rather than an ordering.
#undef K0
#undef M0
#undef HA
#undef HB
#undef HC
#undef HT
#undef EBASE
#undef EADDR
#undef NEND
#undef CHAIN
#undef KNOD_BPF_HASH_NEXT_END
#undef KNOD_BPF_HASH_NEXT_MASK
#undef ELEM_OFF_NEXT
#undef ELEM_OFF_KV

#endif
