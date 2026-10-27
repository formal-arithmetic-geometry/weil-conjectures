## What changed

The statement of `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`
is unchanged, including all universes and hypotheses. Its proof now constructs a normalized
presentation, takes the scalar mate transpose, proves invertibility through the finite-ring
proper scalar map and jointly conservative derived evaluations, and derives the mixed
coefficient square from the coefficient cocycle using dependent congruence.

The single-ring restriction normalization and coefficient cocycle are isolated in
`Sheaf.Paper.EtaleSingleCoefficientProjection`; its proper coefficient-chain input is the
existing proved theorem `finiteCoefficientDirectImageMap_coefficientChain`, pasted with
`etaleOpenScalarComparisons.successive_scalar` by naturality. The system
construction, evaluation normalization and coefficient coherence are separate source results,
recorded as named intermediate theorems with complete proof descriptions and DAG nodes.
They concern distinct parts of the original argument and none restates the item.

The item and all new files retain the module header and use private proof imports. No existing
signature, definition, public import or source-library declaration is changed. No module is
withdrawn and no forced adaptation is needed.

## Proved and sorry left

Original item: one hole closed, in
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`; zero holes left
in that module. This is a decomposition, not a sorry-free proof of the full mathematical
result: three new holes remain, for a net increase of two holes in this packet.

The remaining holes are:

- `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjectionTheory_nonempty`
  (`lem-pur-etale-system-projection-existence`): construction of the normalized sequence-site
  operations and their comparison data.
- `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_evaluation`
  (`lem-pur-etale-system-projection-evaluation`): identification of the evaluated scalar mate
  with the published proper/open coefficient map.
- `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_coherence`
  (`lem-pur-etale-system-projection-coherence`): coefficient composition and the scalar unit
  before evaluation.

The main proof's private helpers establish the transpose, ordinary joint reflection of
isomorphisms, the finite-ring compact scalar isomorphism, and its lift to system projections.
The new single-ring theorem and its private normalization calculations are proved from
existing library results; they add no hole.

The main theorem compiles cleanly through `lcompile.py`. Final packet compilation and delivery
checks are recorded by `deliver3.py`.

## No longer needed

The item removes these unused proof imports:

- `Sheaf.SixFunctors.EtaleOpenTensor`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit`
- `Sheaf.Paper.RingedCoefficientProjectionCocycle`
- `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`

Its direct DAG proof now uses the four intermediate results, the existing proper coefficient
helper, and the mate definition. The original direct dependencies are replaced accordingly.
The system existence node still needs semilinear sections, scalar adjunctions, level left
extension and derived pushforward composition; evaluation still needs the open tensor and
restriction-counit normalization; system coherence still needs coefficient cocycle and
successive scalar normalization. Thus removal of those direct imports does not claim that
these modules disappear from the targets' closure.

`lem-pur-change-of-rings-tensor-comparison`, `lem-pur-derived-change-of-rings`, and
`lem-pur-etale-support-projection-shift-unit` are no longer direct proof dependencies of this
item. The old levelwise tensor argument for invertibility is replaced by the already proved
`proper_scalarMate_isIso` and the open scalar isomorphism. The corresponding public imports
required by the existing file interface are preserved. No whole module is claimed pruned.

The obsolete direct `tool_uses` approvals removed from this item are
`lem-coef-semilinear-derived-sections`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-pur-ringed-coefficient-projection-cocycle`, `lem-coef-etale-open-tensor`,
`lem-sfb-successive-derived-quotient-normalization`, and
`lem-pur-ringed-coefficient-restriction-counit`. Their mathematical work remains in the
new system nodes where listed; the existing mate-definition approval is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically compatible with this reduction. Its levelwise
invertibility step does not need a fresh tensor/projection comparison: the stronger proper
scalar-mate helper already proves it for a finite source ring and an arbitrary target ring.
The finite-field and prime hypotheses remain in the unchanged statement although this route
does not need them.

The mixed-square clause follows from the coefficient cocycle, but its equality is dependent:
destructing equality of composite natural transformations fails in Lean. Applying
`congr_arg_heq` to the dependent family of projections gives the required heterogeneous
equality directly.

The original blueprint unit route is retained. Empty source schemes, zero coefficient rings,
identity coefficient maps and nonflat transitions are allowed in every intermediate statement.
For the zero ring the module categories are trivial; for identity maps the normalized scalar
unit is the unitor. The construction and normalization steps use only actual module functors,
exact localization and adjunction uniqueness, so they do not introduce arbitrary witness data
or infer equality of derived maps from evaluation.

No definition repair, source-library edit, or target-statement change is made.

## New nodes

`lem-pur-etale-system-projection-existence` records only the construction of `Theory`, without
any projection isomorphism, evaluation equation or coefficient cocycle. Its attached module
is `Sheaf.Paper.EtaleSystemProjectionExistence`.

`lem-pur-etale-system-projection-evaluation` records the level-normalization equation for an
arbitrary normalized presentation. It asserts neither existence of that presentation nor
invertibility of the coefficient map. Its attached module is
`Sheaf.Paper.EtaleSystemProjectionEvaluation`.

`lem-pur-etale-system-projection-coherence` records the coefficient cocycle and unit before
evaluation, without asserting existence or invertibility. Its attached module is
`Sheaf.Paper.EtaleSystemProjectionCoherence`.

`lem-pur-etale-single-coefficient-projection` records the separate ordinary single-ring
adjunct normalization and coefficient cocycle. Its attached module is
`Sheaf.Paper.EtaleSingleCoefficientProjection`.

Mathlib searches are the actual LeanFinder, qualified Loogle and source-grep queries recorded
in `searches.jsonl`; mate identities were found and used, but no search returned these
normalized sequence-site results. The imported blueprint was searched for coefficient
projection and semilinear derived constructions; it has the finite-direct-image result used
for the single-ring factor, but no duplicate of the system construction or normalization.
No change record is required because all existing statements and definitions are preserved.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
