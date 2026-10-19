## What changed

Completed the proof of `AlgebraicGeometry.Etale.connected_etale_perfect_constant`.
The proof chooses a geometric point, obtains etale-local bounded constant models,
identifies all nonempty local models by exact geometric stalks and connectedness,
proves pseudo-coherence and finite Tor amplitude of the common stalk, and applies the
Noetherian perfectness criterion. It then applies the weakly contractible common-model
lemma to obtain the final pro-etale clause. The target statement, definition
`geometricStalk`, and all public signatures are unchanged.

Added and proved the two proof-support modules
`Sheaf.SixFunctors.GeometricStalkTensorConstantSingle` and
`Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels`. The first supplies the
stalk/derived-tensor comparison used for Tor amplitude. The second constructs a finite
affine refinement, assembles the componentwise derived isomorphisms, and descends them
along a section supplied by weak contractibility.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.connected_etale_perfect_constant`, node
`lem-sfb-connected-etale-perfect-constant`. Added 0 holes and split off 0 statements.
The two support modules contain no `sorry`; no `sorry` remains in this delivery.
There are no sorries in definitions and no new axioms.

## No longer needed

Removed the unused proof-only imports from the original item:
`Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`,
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`,
`Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`,
`Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`,
`Sheaf.RingTheory.IndEtaleStability`,
`Sheaf.Paper.PbcActualScalarPullback`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`,
`Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`,
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.SixFunctors.GeometricInverseImageConstantModule`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
Their planned dependency nodes are not used by the completed route. The unit route is
retained: bounded constant models, exact stalks, perfectness, and weakly contractible
trivialization all occur explicitly. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report belonged to an unrelated pro-etale products item and did not
describe this module. The current DAG proof plan was realizable directly after adding the
two declared support nodes. No target statement or mathematical hypothesis required
repair. Both support statements were checked at zero modules/rings and empty or
disconnected weakly contractible objects as documented in their module docstrings.

## New nodes

`lem-sfb-geometric-stalk-tensor-constant-single` is the proved derived stalk/tensor
comparison, implemented in
`lean/Sheaf/SixFunctors/GeometricStalkTensorConstantSingle.lean`.
`lem-sfb-wcontractible-etale-constant-models` is the proved weakly contractible
trivialization, implemented in
`lean/Sheaf/SixFunctors/WeaklyContractibleEtaleConstantModels.lean`.
Both node copies and their Lean records are included in the sandbox.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
