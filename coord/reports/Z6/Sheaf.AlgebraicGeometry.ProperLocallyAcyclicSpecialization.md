## What changed

Proved `AlgebraicGeometry.Etale.isIso_etaleStalkSpecialization_of_proper_locallyAcyclic`
in its assigned module, preserving its full signature and all public imports. The proof
follows Stacks Tag 0GJW: proper-base-change fibre isomorphisms, torsion of the affine
higher image, strict-local restriction, invertible cospecialization, then compatibility.
All supporting lemmas added to this module are private and fully proved. No definitions
or statements were changed. The node proof and dependency list now describe the Lean argument.

The final exact-stalk passage is proved rather than assumed: the right-derived natural
transformation unit equation on a bounded-below representative, localization/homology
comparison, and `NatTrans.app_homology` transfer invertibility to specialization on H^q.
The strict-local restriction helper uses every integer degree and cancels the additive
equivalences in `exists_addEquiv_strictLocal_derivedGlobal_exchange`.

Added proof imports:
- `WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf`
- `WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.Paper.StrictHenselizationPointEvaluationProperties`
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`

Validation: the final single-file compilation through the prescribed server wrapper
passed with no errors or warnings in 40.4 seconds. Delivery preflight compiles and
probes all declarations. No new public interface or consumer
adaptation is required. The unit route through proper base change is preserved.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isIso_etaleStalkSpecialization_of_proper_locallyAcyclic`
(node `lem-weil-pbc-proper-locally-acyclic-specialization`).
Added 0 holes; split off 0 statements; 0 holes remain in the delivered module.
Existing imported theorems retain their independent obligations; no imported proof
was replaced or silently assumed beyond its already declared statement.

## No longer needed

A source-import graph comparison adds no library modules to this item's import closure
and removes `Sheaf.Paper.StrictlyHenselianEtaleAcyclic` from that closure.
No newly reached library module or proof obligation is introduced.

Removed these direct proof imports:
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit`
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`
- `WeilConjectures.Mathlib.RingTheory.Henselian`

The existing `lem-weil-pbc-inverse-image-stalk-germ` dependency is replaced by the
already proved `lem-weil-pbc-inverse-image-torsion` API; no germ compatibility equation
is needed merely to transfer torsion. The explicit closed-immersion dependency is
unnecessary because Mathlib supplies proper/qcqs permanence directly.

Removed obsolete top-level tool approvals for
`lem-weil-pbc-strictly-henselian-etale-acyclic`,
`lem-weil-pbc-strictly-henselian-sections-stalk`,
`lem-weil-pbc-derived-exchange-termwise`, `def-weil-pbc-underived-exchange`, and
`def-weil-pbc-cohomology-pullback`. Their former direct representative calculation
is encapsulated by the already stated strict-local derived-global-exchange theorem.
The old functoriality dependency is replaced by its needed local-structure and
point-evaluation-properties declarations; no general strict-henselization functorial
morphism is needed here. These are removals from this proof's immediate dependencies;
other library arguments may still use all these modules and nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The original module still imported five
obsolete dependencies that its node's existing review had already identified for removal.
The plan's final homology passage required some genuine generic Lean glue, supplied here
as the private, fully proved `exact_nt_homology`. The proper-base-change restriction step
is proved from the named strict-local comparison, with no new intermediate holes.

The added existing tools give only strict-local ring structure, surjectivity of canonical
evaluation, preservation/detection of torsion, and negative-degree vanishing. They implement
the same steps of the original route and do not replace any blueprint unit's argument.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
