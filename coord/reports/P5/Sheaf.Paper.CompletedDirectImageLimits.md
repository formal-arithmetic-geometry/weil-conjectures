## What changed

In `Sheaf.Paper.CompletedDirectImageLimits`, prove the normalized K-injective uniqueness
theorem for tower evaluation, the compatibility of the ordinary reduction/pullback
isomorphisms with all quotient transitions, and the normalized unique derived
reduction/pullback comparison. All 25 existing public signatures and all original
docstrings are preserved. The comparison predicate is definitionally factored through a
generic version of its existing equation; no mathematical condition changes.

Evaluation uses the uniqueness of the two universal right-derived pairs. The ordinary
comparison uses the scalar-adjunction unit identity, the formula on sheafified tensor
generators, and naturality of the finite ring identifications. `NatTrans.ofOpSequence`
handles arbitrary transition maps, including identities. The derived comparison descends
along the localization of the K-flat subcategory; flat-term K-flat resolutions supply a
smaller resolving class on which pullback preserves K-flatness. Its characterization still
quantifies over every K-flat complex, without adding a flat-term hypothesis.

The proof helpers are private and proved. One new public definition,
`IsDerivedReductionPullbackComparison`, states the same normalization equation for general
abelian categories; the existing comparison predicate specializes it. It is a proposition
with a concrete formula, containing no postponed proof or data. General tensor helpers are
imported privately from `ConstantTowerDirectImageNormalization` and
`ProEtaleRingSheafChangeAdjunction`. The general localization argument is adapted from
`ProEtaleConstantReductionTower`, which cannot be imported because that module already
depends on this one. `AdicCoefficientDatum` is imported with its private interface so
simplification reuses its generated counit equation instead of creating a duplicate when a
later consumer loads that interface. Additional private imports provide the exact
functor/right-derived composition comparison, right-fraction density, flat-term K-flat
resolutions, and ringed-topos preservation of K-flatness.

The existing DAG node records these arguments and their dependencies. There are no
statement changes, no consumer adaptations, and no new nodes. The sole definition-body
refactoring preserves the old equation by definitional equality.
`coord/changes/p5-completed-direct-image-proof-local-commands.md` documents the local
elaboration commands and the comparison-predicate refactoring. The evaluation preservation
helper is a proved private theorem, registered as a local instance only in the section
containing the private normalization lemma. Its registration ends before the public
evaluation-existence theorem; public definitions and later instance searches therefore use
their original interfaces. It adds no global instance.

Validation: `lcompile.py` accepted the complete module in 38.2 seconds after the
generic-predicate and private-interface refactorings. All 25 original declaration signatures are unchanged, all
added imports pass the import-cycle check, and every production line has at most 100
characters. K-injective preservation is packaged at the general-category level and
registered only while checking the private normalization lemma. A general proved
conservativity lemma also factors the existing tower-projection isomorphism proof through
levelwise homology. The derived comparison uses explicit functor and counit arguments and
the pointwise abelian structures of the tower categories, preserving its normalization.
The generic predicate prevents the existence proof from repeatedly comparing the expanded
concrete coefficient-category formulas. No compile limit is changed. The downstream scan
identifies nine consumers and no consumer directly mentioning
`IsCompletedReductionPullbackComparison`. All nine unchanged consumers compiled
against the candidate. A separate example copied the original predicate formula
verbatim and proved its equivalence to the refactored predicate by `Iff.rfl`
(33.9 seconds). Temporary verification sources and artifacts are excluded from
the delivery.

## Proved and sorry left

Four of the six holes in the current shared source are closed:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerPushEvaluation_existsUnique`.
- `AlgebraicGeometry.Scheme.completedOrdinaryReductionPullbackInv_isIso`.
- `AlgebraicGeometry.Scheme.completedReductionLevelPullbackIso_transition`.
- `AlgebraicGeometry.Scheme.completedReductionPullbackIso_existsUnique`.

The session began from a five-hole snapshot carrying T1's proved ordinary-mate
isomorphism (review metadata: landing `20261020T221350-L-4178472`). The current
shared snapshot has that theorem holed again. This packet preserves its already
proved body and has compiled it together with the three new proofs. Thus the
current-source comparison is four closures, while three are new work in this session.

Two original holes remain, both attached to `prop-weil-pbc-direct-image-limits`, with
their original source and proof docstrings:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlim_roos`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection_properties`.

No holes are added or split off. The remaining two theorem bodies are unchanged. The three
closed proofs use existing declared dependencies, including the universal reduction-tower
counit and its K-flat computation theorem.

## No longer needed

Remove these unused direct proof-import edges (their required interfaces are already
available through the retained imports):

- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.CompletedDerivedInverseLimit`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.
- `Sheaf.Paper.KoszulReconstruction`.
- `Sheaf.Paper.PerfectProjectionFormula`.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.Algebra.Homology.RoosComplex`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.

No module or node is withdrawn. In particular the remaining Roos and projection clauses
still need their planned dependencies; zero direct consumers of the Roos theorem is not
being treated as a reason to discard its statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The strict reduction/pullback comparison can be
constructed directly from the actual ordinary coefficient-change mates and K-flat
localization, before invoking the diagram-site projection argument. The DAG now records
this implementation explicitly. The blueprint unit's own statement and proof steps are
retained.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
