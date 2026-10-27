## What changed

Wrote proofs for all seven clauses of
`AlgebraicGeometry.ClosedSourceSiteTensor.closedSourceSiteTensorComparison`.
The section formula follows from monoidal normalization of the standard base-change
mates, their localization evaluations, and the comparison adjunction unit.
Proved the ordinary comparison and arbitrary scheme pullback multiplication squares by
cancelling the tensor of the epic constant-restriction maps. The constant-unit
normalizations identify the remaining maps, avoiding the planned local lifting argument.
Proved support-change normalization directly from adjunction and lower-star composition.
Proved a general private degree-zero derived-square lemma using the single-complex
tensor isomorphism and the canonical exact left-derived functor comparison, and
applied it to both ordinary squares. Updated the node proof and dependencies to
this route. All target signatures and original public imports are retained.
The proof argument in `intersectionChange` was made explicit; its constructed map
and its type are unchanged. The normalization dependency factors its identical pro-etale adjunction transpose
through the new generic data definition `closedTranspose`; its internal private
mate lemmas use the same interface. See
`coord/changes/supported-constant-closed-transpose.md`. The comparison-pullback
construction also receives its native module-valued source and target explicitly,
with the identical generic comparison as its body; see
`coord/changes/supported-constant-comparison-pullback-interface.md`.
The section-evaluation isomorphism is expressed via weakly etale base change and
terminal evaluation, equal to its previous localization formula by localization
naturality and pullback uniqueness; see
`coord/changes/closed-source-section-evaluation.md`. These reached definitions
are flagged for independent statement review. The etale exchange and comparison
section maps also use native interfaces for the identical canonical maps; see
`coord/changes/closed-source-etale-section-interface.md` and
`coord/changes/closed-source-comparison-section-interface.md`.
No target signature changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ClosedSourceSiteTensor.closedSourceSiteTensorComparison`
(node `lem-pur-closed-source-site-tensor-comparison`).

Holes closed: 1 of 1. Holes added: 0.
Sorries left in the assigned module: 0. The normalization dependency had 0 holes
before this repair and still has 0; its data constructions and private helper
proofs contain no postponed proofs.
All private helpers are proved; no statements are split off. The final isomorphism
checks are factored through generic proved lemmas to keep concrete section types
from unfolding their sheafification constructions during elaboration.

Validation: the complete assigned module passes `lcompile.py` in 55.5 seconds,
with no Lean warnings or errors. The normalization dependency passes in 44.7
seconds. The module uses sequential elaboration and contains no profiler options.
The main theorem's signature is byte-for-byte identical to the repository source;
all original public imports are retained. Both delivered modules have zero holes,
and all Lean source lines satisfy the 100-character limit.

## No longer needed

The proof no longer imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`.
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Mathlib.CategoryTheory.Sites.EpiMono`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`.

The corresponding proof route through underlying set sheaves, local lifting of
sections, and a separate ringed-topos tensor comparison is unnecessary: the existing
module-valued localization, monoidal adjunction, and derived functor APIs suffice.
Removed these original proof dependencies from this node (the first seven also
withdraw the corresponding obsolete top-level `tool_uses` approvals):

- `lem-cbc-comparison-pullback-sections`: the module-valued localization and
  comparison-unit calculation proves the required formula directly.
- `lem-pe-constant-left-module-inverse-image`: constant inverse image is identified
  with the oplax unit through its existing adjunction definition.
- `lem-cbc-abelian-etale-proetale-cohomology-comparison`: only the degree-zero
  comparison unit at the terminal object is required.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`: no passage to underlying sets.
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`: no local lifting argument.
- `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`: the existing strong
  monoidal functors and their natural oplax comparisons suffice.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the stated `DerivedSquare`
  already uses the canonical fixed-coefficient left-derived tensor comparison;
  its counit identity proves the required transport directly.
- `def-weil-pbc-constant-sheaf`: no separate proof dependency beyond the existing
  constant sheaf definitions used in the statement and unit normalization.
- `def-pur-sheaf-tensor-product`: the existing module-valued tensor and cochain
  bifunctor APIs suffice; no independent ringed-module tensor construction is used.

These are dependencies removed from this proof, not claims that their modules are
absent from every target's import closure. No module is withdrawn. The unit
`sk-prop-a1-kummer` and all its realized statement/steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned local pure-tensor calculation is longer than needed. Right exactness of
tensor and the supplied cokernel presentations make the constant-restriction tensor
epic, so monoidal unit normalization determines the multiplication square directly.
No mathematical statement is changed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
