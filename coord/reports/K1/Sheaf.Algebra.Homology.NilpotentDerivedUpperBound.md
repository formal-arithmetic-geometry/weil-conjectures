## What changed

Completed `DerivedCategory.isZero_homology_of_nilpotent_derived_reduction` without changing
its signature. Private helpers construct the equivalence between modules on the one-object
bottom-topology site and ordinary modules, its tensor and scalar-extension comparisons,
and preservation of flatness and K-flatness. The ordinary-module proof combines the existing
source derived tensor upper bound and K-flat single-module tensor model with nilpotent
filtration by `IM` and the homology sequence of a short exact sequence.

The supplied left derived functor is compared with the canonical one by the uniqueness
isomorphism for left derived functors; no particular model, universe equality, boundedness
of the original complex, or extra flatness hypothesis is imposed. The original statement
and all public imports remain unchanged. Helper typeclass registrations are explicitly local. The main node records the actual proof route.

Two new DAG attachments expose already proved source declarations used for the shorter
route. They add no Lean modules, declarations, or holes. No other module is adapted.

## Proved and sorry left

Closed the one original hole in
`DerivedCategory.isZero_homology_of_nilpotent_derived_reduction`
(node `lem-weil-pbc-nilpotent-derived-upper-bound`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean module: none.
All private helpers are proved. This is a proof, not a decomposition.

The final remote single-file compile passed cleanly in 21.7 seconds. `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`; there is no imported `sorryAx` either.
A normalized textual comparison confirms the main theorem's complete signature is unchanged.
The required delivery dry run passed: the delivery compiles and passes preflight. The filtration
includes the exponent-zero base case; the argument also covers zero rings, the zero ideal,
and arbitrary negative upper bounds, and does not assume the input complex bounded.

## No longer needed

The assigned proof no longer needs these original planned dependencies directly:

- `lem-pc-kflat-bounded-flat-replacement` / `Sheaf.Algebra.Homology.BoundedFlatReplacement`.
- `lem-pc-kflat-cone-direct-sum` / `Sheaf.Algebra.Homology.KFlatClosure`.
- `lem-pc-module-bounded-flat-kflat` / `Sheaf.Algebra.Homology.BoundedFlatKFlat`.
- `lem-pur-acyclic-kflat-tensor-arbitrary` / `Sheaf.Algebra.Homology.AcyclicKFlatTensor`.
- `lem-pur-kflat-change-of-rings` / `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `lem-pur-quasi-iso-cone-acyclic` (no direct cone argument remains).

The truncation/replacement/cone steps are replaced by `DerivedCategory.isLE_tensor` and
`DerivedCategory.QObjTensorSingleFunctorObjIso` from the existing proved source library.
Ordinary-module K-flat base change replaces the sheaf-level change-of-rings K-flat tool.
The obsolete entries above are removed from the main node's `proof_deps` and `tool_uses`.
These are removals from this proof's route; a module may remain needed elsewhere.

Also removed the unused proof imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The direct source flat-resolution import supplies the ordinary-module instance needed by
the existing derived tensor API.

## Where the brief, the DAG or earlier work was wrong

The statement and the nilpotent-filtration argument are correct. The planned construction
of a bounded-flat model and its cone comparison is unnecessary because the source library
already proves the needed upper bound for derived tensor products. The independent
coefficient-universe imports are unnecessary on the existing one-object site; the original
`HasDerivedCategory.{w}` assumptions are retained exactly.

## New nodes

`lem-weil-pbc-source-derived-tensor-upper-bound` attaches the existing proved source lemma
`DerivedCategory.isLE_tensor` in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.
It supplies the upper bound `b + 0` after tensoring with a module in degree zero.

`lem-weil-pbc-source-kflat-tensor-single-model` attaches the existing proved source definition
`DerivedCategory.QObjTensorSingleFunctorObjIso` in the same module. It identifies derived
tensor of a K-flat complex with a single module with termwise tensor. Both are source reuse,
not split-offs, and neither leaves work for another worker.

Change record: `coord/changes/k1-nilpotent-derived-proof-context.md` documents the added
proof context conservatively flagged by preflight; no existing interface is changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
