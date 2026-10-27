## What changed

Replaced the proof of `WeilConjectures.GeneratorReduction.tensorAdjunctionReductionSquares`
with a calculation through ordinary word comparisons. The existing public signatures and
all operation definitions remain unchanged. Private helpers handle tensor coherence from
internal-Hom compatibility, mates of proper and open adjunctions, recursive naturality,
and cancellation of the short-word completion transport. Added a private Mathlib import
for the finite-field characteristic calculation. Local irreducibility attributes
keep the chosen coefficient-calculus witness and standard category constructions from
being unfolded during routine rewrites. Recursive word equations are reduced directly,
avoiding generation of their large global simp equations.

Added `Sheaf.SixFunctors.CanonicalReductionPullComposition` for the independent geometric
compatibility of the specified whole-system pullback comparison with composition. Its
statement uses only the operation, compositor and realization data, not generator coherence.

## Proved and sorry left

The original hole is `WeilConjectures.GeneratorReduction.tensorAdjunctionReductionSquares`
(node `lem-sf-tensor-adjunction-reduction-squares`). Its proof reduces to the existing
short-word completion helper and reconstruction theorem and the new canonical
pullback-composition theorem. This is a decomposition: one original hole replaced by one
strictly smaller new hole, not a net hole closure.

The only new sorry is
`WeilConjectures.GeneratorReduction.canonicalReductionPullComposition`
(node `lem-sf-canonical-reduction-pull-composition`). The item module has no sorry.
The existing `WeilConjectures.GeneratorReduction.completionMap_isIso` is proved in the
current shared source and is separately recorded by
`lem-sf-short-word-completion-isomorphism`; this delivery does not change it.
No definition contains sorry. Counts: original holes 1; removed 1; added 1; retained in
the item 0; net closure 0. Full proof checking succeeded during profiling; the final delivery
checks validate the cleaned sources and the per-file compile limit.

## No longer needed

Removed direct proof imports of `Sheaf.Paper.RingedExchangeTensorCoherence`,
`Sheaf.SixFunctors.IntegralOpenReductionComparison`,
`Sheaf.Paper.BasicOperationsCoefficientReduction`, `Sheaf.Paper.SemilinearDerivedSections`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices` and `Sheaf.Paper.SfDerivedDirectImage`.
The existing public imports are preserved; their transitive data dependencies remain.

The proof no longer uses `lem-pur-completed-operation-tower-substitution` or its module
`Sheaf.Paper.CompletedOperationTowerSubstitution` as a proof dependency. In particular,
tensor coherence is derived directly from evaluation/internal-Hom compatibility.
The old proof-dependency uses of `lem-sf-integral-open-reduction-comparison`,
`lem-weil-pbc-mate-pasting`, `def-weil-pbc-adjunction-mate` and
`lem-coef-semilinear-derived-sections` are replaced by the specified comparison definitions
and Mathlib's actual mate identities. Removed the obsolete top-level tool approvals for
completed-operation substitution and mate pasting; retained reconstruction.
These are removals from this proof's route. No upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned completed-operation substitution theorem supplies a unique transported
structural arrow, but its Lean statement does not identify that arrow with this item's
independently specified ordinary ringed-site arrow. Applying it alone does not prove the
required geometric square. The replacement tensor calculation uses the stronger relevant
normalization already present in the actual coefficient calculus. Pullback composition
needs the separate canonical compatibility lemma stated here.

The published `completionMap_isIso` helper was attached only to the parent generator
coherence node. The present argument uses this independent helper, never the theorem
`generatorReductionCoherence`. Added a node recording precisely that existing helper so
the dependency is not presented as an application of the parent theorem. The existing
parent data module publicly imports completed-operation substitution; that import is
preserved and prevents claiming the whole module has become globally unnecessary.

New statement edge checks: identity maps, zero complexes and arbitrary unbounded inputs
use the same ordinary projection identity and localization. The geometric compatibility
has no properness or completeness requirement. Inverse open mates are used only at
objects where the primitive formulas and normalized reconstruction prove invertibility.
There is no assumption that a mate of an isomorphism is globally invertible, and no
faithfulness inference from finite derived evaluations.

## New nodes

`lem-sf-canonical-reduction-pull-composition` records the genuine geometric part shared by
the pullback and proper direct-image compositor cases. Its Lean statement is in the new
module of the same topic. Its proof in words goes through ordinary projected sections,
adjoint conjugation and K-flat localization. This is strictly part of the original
nine-generator assertion, not the assertion renamed or repackaged.

`lem-sf-short-word-completion-isomorphism` records the already-existing declaration
`completionMap_isIso` in `GeneratorReductionStatement`. No second Lean declaration,
module or sorry is introduced for it. Its current proof uses primitive completion
effectivity and the short-word integral-domain theorem. No existing statement or
non-theorem definition has changed, so there is no definition-change record.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
