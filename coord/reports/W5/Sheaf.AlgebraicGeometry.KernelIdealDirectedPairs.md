## What changed

Proved `AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernelIdeal_directed_pairs` in
`Sheaf.AlgebraicGeometry.KernelIdealDirectedPairs`, preserving its full signature.
The proof constructs generated ideals and quotient objects from the existing quotient
lemma, factors maps between kernel modules using their injective section maps, applies
finite-presentation Hom-colimit factorization, and constructs the directed preorder and
quotient functor. Quotient uniqueness proves both functor laws and compatibility.

Private proved helpers provide the underlying module map of an algebra map, sectionwise
kernels, factorization through an injective module inclusion, affine detection of zero,
and extension of the quotient kernel formula from affine opens to every open.
All added imports are private proof imports. The change record
`coord/changes/W5-kernel-ideal-directed-pairs-proof-options.md` documents the
declaration-scoped elaboration/lint options requested by preflight. Updated the node proof to describe these
arguments and the removed finite-presentation quasi-coherence dependency.

Validation: the complete proof compiled through lcompile.py. Final delivery runs the
project preflight and its compilation/axiom checks. No statements or definitions used
by consumers change; no consumer adaptations are required.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernelIdeal_directed_pairs`
(node `lem-weil-pbc-kernel-ideal-directed-pairs`). Proved 1 of 1 holes.
No holes remain in the item module; no holes added; no split-off statements.
The proof uses the existing declarations
`generated_ideal_quotient_quasiCoherent` and
`hom_directedColimit_of_isFinitePresentation`, whose proofs remain separate items.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` and the node dependency
`lem-weil-pbc-quasi-coherent-finite-type-affine`: Mathlib's
`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation` supplies exactly the needed
quasi-coherence directly. All other original imports and the two remaining proof
node dependencies are retained. No module is withdrawn. Temporary experimental
imports of the source Modules.Sheaf and Modules.Presheaf API were removed; the proof
uses Mathlib interfaces directly.

## Where the brief, the DAG or earlier work was wrong

No false statement found and no unit-route change. The quotient dependency explicitly
states its kernel formula only on affine opens, whereas this item requires every open.
The private `quotient_kernel` proof fills that gap by affine detection and categorical
kernels/cokernels. The DAG's quasi-coherence dependency was unnecessary because the
same fact is already a Mathlib instance. Zero modules, empty schemes, noninjective
transition maps and preorders without antisymmetry require no extra hypotheses.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
