## What changed

Proved `IsDiscreteValuationRing.finite_tame_character_tower` with its original signature.
The private, fully proved helpers implement the two arguments of Stacks Tags 0BSX and
0BU7: lifting decomposition/inertia automorphisms and comparing local uniformizers.
Further private lemmas lift wild elements by a coprime power and rescale the characters.
The final assembly uses `finite_normalization_tame_inertia` at both levels, proves
prime-to-p divisibility, and establishes the canonical-character transition formula.
No new public interface, definition, or deferred theorem is introduced.

Updated the item's DAG proof to reflect the direct invariant-ring argument: a fixed
upper integral element lies in L by the finite Galois fixed-field theorem, and its
integrality descends along L -> M. The quotient residue-action API applies because
the primes are maximal. This avoids installing fraction-field structures on the
normalizations merely to use the invariant-ring lifting results.

Searches: LeanFinder found ramification-index tower formulas but no combined character
compatibility theorem; Loogle found the inertia membership API; grep found the local
ring equivalence, uniformizer factorization, and quotient stabilizer lifting APIs used
in the proof. The library search found no existing theorem of the required form.
Read Stacks `lemma-one-orbit-geometric-galois-compare` (0BSX),
`lemma-compare-inertia` (0BU7), and `remark-canonical-inertia-character` (0BU8).
The trivial tower and trivial tame/wild groups are included: no nontriviality of
these groups is assumed; positive valuation follows from the local nonunit condition.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsDiscreteValuationRing.finite_tame_character_tower`
(node `lem-exc-finite-tame-character-tower`). Added zero holes; split off zero holes.
There are no `sorry`s left in the delivered module. All private helpers are proved.
The existing dependency `IsDiscreteValuationRing.finite_normalization_tame_inertia`
still has its independently assigned proof hole; it is unchanged by this delivery.

## No longer needed

Removed proof imports `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and
`Mathlib.RingTheory.Localization.Integral`. Replaced the broader
`Mathlib.RingTheory.Invariant.Galois` with `Mathlib.RingTheory.Invariant.Basic`.
The direct fixed-element construction avoids
`lem-weil-pbc-integral-closure-algebraic-extension-normal` as a proof dependency;
its fraction-field and normal-domain structures are unnecessary for this argument.
All other declared dependencies remain used. The required unit route is preserved.
The earlier sandbox's two unpublished helper modules were consolidated into private
proved lemmas in this item; neither was present in the shared library, so there are
no library modules to withdraw.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had complete supporting proofs but no report or delivery and one
maxHeartbeats linter warning. Its two helper modules are unnecessary as public modules;
they are proved private components of the assigned theorem. The mathematical statement
and the source's route require no correction. No target or other module was changed.

The resumed dry run flagged section-level
`variable`/`include` commands as an interface change. Replaced those commands with
explicit parameters on the three private restriction lemmas; their mathematical
signatures and the public interface are unchanged.

Verification on resumption, 2026-10-19: the public theorem signature is textually
identical to the current shared source, the sandbox has zero `sorry`s, and the
only changed node fields are `proof`, `proof_deps`, and `proof_origin`. Every Lean
line is at most 100 characters. The supported single-file `lcompile.py` command
compiled the retained proof cleanly in 26.8 seconds (exit code 0). The previous
attempt's compile-server failures are resolved for this single-file check.
The required delivery dry run and final push supply the remaining delivery checks.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
