## What changed

Proved `AlgebraicGeometry.eventually_finite` in the assigned module. The proof first applies
`eventually_affine`, then works on each member of a finite affine cover. A private affine-tail
lemma descends the finitely many monic relations through the filtered colimit of global sections,
uses finite algebra generators and finite module transitivity, and finally takes a common upper
bound of the finitely many stages. The proof uses the existing `exists_appTop_map_eq_zero_of_isAffine_of_isLimit`
lemma from Mathlib's affine transition limit development.

## Proved and sorry left

Closed the sole sorry, `AlgebraicGeometry.eventually_finite`. No sorries remain and no new public
statement was added.

## No longer needed

The original proof-plan dependencies for affine-pair finite-type characterization, explicit
filtered-colimit elementwise equality, finite-of-integral-generators, and finite-local/composition
lemmas are not imported as separate Sheaf declarations: the proof uses Mathlib's global-sections
vanishing lemma, `RingHom.Finite`, `Algebra.finite_adjoin_of_finite_of_isIntegral`, and the
`IsFinite` morphism property directly. No DAG nodes are removed; all existing public imports of
the assigned module remain valid.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan is mathematically sound but more finely split than needed in Lean. Mathlib's
`exists_appTop_map_eq_zero_of_isAffine_of_isLimit` packages the filtered-colimit equality descent,
and `IsFinite` already supplies finite composition and open restriction, so those planned helper
nodes were unnecessary for this implementation.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
