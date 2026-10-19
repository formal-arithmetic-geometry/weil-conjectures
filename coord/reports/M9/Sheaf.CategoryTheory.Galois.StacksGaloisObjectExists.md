## What changed

Proved `CategoryTheory.exists_stacksGaloisObject_hom_of_isConnected` in
`Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists` without changing its signature.
Lifted the given set-valued functor to `FintypeCat` using its existing finite-value
proofs. Constructed local Mathlib Galois-category and fibre-functor instances from
the Stacks axioms and the already-proved `stacksGalois_mono_complement`.
Applied Mathlib's `exists_hom_from_galois_of_connected`, then its bijective
automorphism evaluation to recover the project's connectedness/cardinality predicate.
Finite groups are transported to the small universe before invoking finite colimits;
`FintypeCat.uSwitch` provides the fibre functor in the hom universe required by Mathlib.

Added proof-only imports of `Sheaf.CategoryTheory.Galois.StacksMonoComplement` and
`Mathlib.CategoryTheory.Galois.Decomposition`. Updated the existing node's proof,
proof dependencies and proof origin to record this route. No definitions, public
signatures, targets or consumer modules changed, and no new modules or nodes were added.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.exists_stacksGaloisObject_hom_of_isConnected`
(node `lem-galois-object-exists`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered Lean file.

Validation: the delivery tool's remote compilation and axiom probe passed.
Preflight initially flagged an added file-level `open` command; this was removed
and the limit names qualified within the proof. The final delivery reruns all checks.

## No longer needed

Removed the redundant proof-only import
`Sheaf.CategoryTheory.Galois.StacksGaloisCategory`: the unchanged public import of
`StacksGaloisAxioms` already publicly exposes the definitions used in the signature.
No library module becomes unreachable as a result of removing this duplicate import.

The direct proof dependency `def-galois-finite-coproduct` is no longer needed here:
its component construction is supplied by the existing mono-complement theorem and
Mathlib's decomposition theorem. This definition remains a transitive dependency;
no project module is withdrawn. All other original declared dependencies are retained.
The explicit tuple/diagonal/stabilizer proof is reused through Mathlib instead of
being duplicated in this module.

## Where the brief, the DAG or earlier work was wrong

The old Mathlib-candidate note correctly observed that the Stacks and Mathlib
classes differ, but it predates the now-proved `stacksGalois_mono_complement`.
That declaration supplies exactly the missing summand axiom. The local comparison
construction is already exemplified in `Sheaf.CategoryTheory.Galois.AbstractEquivalence`;
this proof reuses its construction without importing the equivalence theorem.
Mathlib's Galois-object notion converts back using bijective automorphism evaluation,
so no added assumptions or changed definitions are needed.

The searches through `msearch.py` (LeanFinder, Loogle and grep), and direct searches
of Mathlib, `lean/WeilConjectures` and `lean/Sheaf`, identified the Mathlib existence
theorem, its cardinality API, and the existing complement proof. The unit record
`sk-prop-h2` has no realized statement or proof step attached to this node; the route
change affects only this lower-level argument.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
