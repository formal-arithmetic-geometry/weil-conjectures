## What changed

Proved the finite coefficient counit, balanced projection evaluation and naturality
calculations in `Sheaf.Paper.QuotientDiagramProjectionEvaluation`. The main proof now
constructs a presentation, then assembles those calculations with its transition laws. The direct-image transition
formula follows from the inverse-image formula by the proved adjunction calculation
`push_transition_of_pull`.
The projection calculation reuses the proved generic `projection_evaluation` helper in
`SemilinearDerivedSections`, which applies to any geometric data with the normalized
tensor and counit evaluation equations. Naturality is proved directly from adjunction
transposes and counit naturality.

Moved the 16 existing data declarations, with their namespaces and public re-export, to
`QuotientDiagramProjectionData`. Added the proof-valued `TensorReduction.flatTerms`
field: the existing exact tensor comparison's representative equation requires it.
The canonical construction must prove it; the existence theorem gains no hypothesis.
See `coord/changes/B8-quotient-projection-representatives.md`.

`QuotientReductionTensorEvaluation.reductionTensorEvaluation` proves the tensor
normalization from the ordinary square and the three representative equations. The
proof compares every cochain total-tensor summand, localizes that equality, applies
the generic model-square cancellation lemma, then transports by flat K-flat resolution
isomorphisms. The construction of the ordinary and derived presentation is a separate
source-based result in `QuotientDiagramProjectionConstruction`.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.QuotientDiagramProjection.quotientDiagramProjectionEvaluation`.
Its original binders and conclusion text are unchanged. Its `Presentation` data now also
records the true flat-term preservation property described in the change record.

Added and proved
`SheafOfModules.QuotientDiagramProjection.reductionTensorEvaluation`
(node `lem-pur-quotient-reduction-tensor-evaluation`). Its private cochain and representative
lemmas are proved, with no private holes.

One hole remains, added in
`SheafOfModules.QuotientDiagramProjection.quotientDiagramProjectionConstruction`
(node `lem-pur-quotient-diagram-projection-construction`). This constructs the normalized
presentation and its inverse-image transition formula. It does not assert the coefficient counit,
projection evaluation or arrow naturality. The main proof contains actual proofs of all
three assertions, and the tensor normalization is proved separately.

Thus one original hole is closed and one construction hole is added: this is a
decomposition, with net hole change zero, not a claim of an axiom-free target proof.
There is no `sorry` in a definition, and no arbitrary data is defined by choosing a witness
of the unfinished existence theorem.

## No longer needed

Removed the original proof imports:

- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`
- `Sheaf.CategoryTheory.SystemEvaluationTopos`
- `Sheaf.CategoryTheory.SystemSingleDerivedExtension`
- `Sheaf.CategoryTheory.SystemOrdinarySingleExtension`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.CategoryTheory.SystemSingleDerivedEvaluation`

The main proof no longer directly needs the old singleton/evaluation construction nodes;
they remain dependencies of the retained construction result where needed. In particular,
`lem-pur-system-ringed-sequence-site`, `lem-pur-system-level-left-extension`,
`lem-pur-system-singleton-geometric-pullback`,
`lem-pur-system-singleton-scalar-extension`,
`lem-pur-system-evaluation-scalar-restriction-normalization`,
`lem-pur-strict-quotient-diagonal-normalization`, `lem-pur-system-evaluation-topos`,
`lem-weil-pbc-ringed-projection-mate-exact`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are not declared globally unnecessary.

The main projection calculation does not need
`lem-weil-pbc-ringed-exchange-tensor-coherence`: the already proved generic geometric
projection-evaluation identity supplies that step. The separate Mathlib-leaf dependencies
`det-sp-unique-right-adjoint` and `lem-weil-pbc-adjunction-of-natural-bijection` are not
needed as direct proof dependencies; the proof uses the specified adjunctions and their
hom-equivalence naturality. No existing module or upstream declaration is withdrawn. The construction additionally cites
`lem-weil-pbc-ringed-topos-flat-module-pullback` for its flat-term property.
No claim is made that removing a direct import removes it from every target's closure.

## Where the brief, the DAG or earlier work was wrong

The planned singleton results construct evaluation comparisons but do not themselves
assemble `Presentation`, which additionally contains ordinary scalar units, universal
left-derived reductions, cochain summands and representative equations. The existing
`StrictQuotientDiagonalNormalization` theorem is stated in a uniform small universe,
whereas this item has independent object, morphism and coefficient universe parameters.
It cannot be applied directly as a complete construction of this record.

The earlier `TensorReduction` interface did not include preservation of flat terms,
although applying its tensor evaluation representative equation requires that property
for the ordinary reduced complexes. Added this true property as an explicit proof field.
This strengthens the presentation existence obligation and leaves all normalization
equations intact. Edge checks include zero/unit ideals, the identity geometric morphism,
identity transitions, and nonflat quotient maps: extension of a flat module remains flat
over its target ring in all these cases. No flatness of the quotient as an ambient module
is assumed.

## New nodes

`def-pur-quotient-diagram-projection-data` owns the moved definitions and the flat-term
preservation proof field. Original public names and re-exports are preserved.

`lem-pur-quotient-diagram-projection-construction` is the remaining ordinary/derived
construction result. Its source proof specifies quotient transitions, scalar insertion,
flat-term representatives, tensor multiplication and geometric evaluation normalization.

`lem-pur-quotient-reduction-tensor-evaluation` records the proved cochain and derived tensor
normalization. All new nodes inherit the original chapter and unit; the unit route and
blueprint statement are unchanged. Each records natural-language, type-pattern and
Mathlib-source searches. The interface change record is
`coord/changes/B8-quotient-projection-representatives.md`.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
