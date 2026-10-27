## What changed

Implemented a proof of `WeilConjectures.nativeConstantRestriction_push_quasiIso`
in `Sheaf.Paper.NativeConstantRestrictionAcyclicity`, retaining its exact statement
and all three original public imports. The proof constructs the constant-ring
sequence-site equivalence with independent site and coefficient universes,
identifies scalar restriction using the actual quotient cone and its limit
identities, and identifies sequence-site pushforward with whole-tower pushforward.
It then applies the existing proved `continuous_scalar_resolution` and
`quasiIso_map_of_models` helpers. All added helpers are private and proved.
The item's node describes this argument and records its actual dependencies.
No existing definition, public declaration signature, or consumer is changed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.nativeConstantRestriction_push_quasiIso`
(node `lem-pur-native-constant-restriction-acyclicity`).
The complete proof passed single-file elaboration and kernel checking within
the 60-second limit (49.6 seconds). The compiler's subsequent style suggestions
replace proof-valued `letI` declarations by `let`; delivery checks the final file.

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off statements or new public declarations are added. Every private
helper has a complete proof or an explicit construction. No debugging options
or diagnostic commands remain.

## No longer needed

The direct proof dependencies `lem-pur-system-ringed-sequence-site` and
`lem-weil-pbc-diagram-site-realization` are removed from this node's proof plan.
The native category already is a sequence-site module category; the required
constant-ring equivalence is constructed explicitly using the vertical sheaf
criterion of `lem-weil-pbc-diagram-site-topology`. The small-category realization
cannot directly handle the independent site universes of the actual pro-etale site.

No Lean import is removed; all added proof imports are used. In particular,
`Sheaf.Paper.CompactSupportNativeSystemEvaluation` supplies exported instances
needed to elaborate the unchanged public statement. The source library still
imports SystemRingedSequenceSite transitively through VaryingRingOperations;
removing a direct DAG proof edge does not withdraw that module. No module or
public declaration is withdrawn, and no global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The recorded diagram-site realization uses small categories in one universe;
the actual pro-etale site has objects in universe `u+1` and morphisms in `u`.
The explicit curry/uncurry argument works with these independent universes.
The existing general composition and transport helpers already handle the
large sites, so no additional split is needed. The mathematical statement and
the unit's route are unchanged.

The preserved draft removed a public import needed for implicit instances in
the theorem's signature. This delivery retains the original import. General
section-map transport lemmas avoid expanding the concrete coefficient rings.
In particular, an explicitly typed generic section-map function fixes its target
carrier before the coefficient-system transition is specialized. The level
comparisons are assembled using their existing natural-number indices, with
conversion to arbitrary opposite-index arrows performed in the generic lemma. No change record is required for a public
interface change, because no such change is made.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
