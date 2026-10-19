## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHom_finiteExtension`
with its original signature. All helpers are private and proved in the item module.
A Type 0 normed model of the finite-dimensional field is constructed using Mathlib's
`Module.Finite.small` and `Shrink`. Explicit continuous ring equivalences induce coefficient
sheaf isomorphisms, including the pulled-back closed unit ball. Restriction of scalars and
its exact derived monoidal equivalence transport bounded constructibility and internal Hom.
The existing class-indexed finiteness instance then supplies both conclusions.
No coefficient class, mathematical definition, public signature or consumer module changes.
Validation: the final module compiles cleanly through lcompile.py in 6.7 seconds; its
public signature is byte-identical to the source signature, and no line exceeds 100 characters. The resumed delivery also passed the required
deliver3.py dry run against the freshly fetched base (2026-10-19).

## Proved and sorry left

Closed 1 of 1 item holes: `boundedConstructibleHom_finiteExtension`.
Added 0 holes; split off 0 theorems; no sorry remains in any delivered Lean file.
The existing dependency `isMonoidalClosed_boundedConstructible` remains unproved in its
unchanged source module. The proof uses that declared dependency, not a new assumption.
The retained attempt's two unproved coefficient-class bridges were discarded: the proof
instead transports the closure property, without claiming literal class membership of an
isomorphic universe-generalized coefficient object.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CartesianCoefficientsFiniteFree`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`
- `Sheaf.Paper.ConstructibleInternalHomContinuity`
- `Sheaf.Paper.DerivedInternalHomFilteredColimit`
- `Sheaf.Paper.FiniteCoefficientDescentTwoColimit`
- `Sheaf.Paper.FiniteFieldInternalHomFiniteness`
- `Sheaf.Paper.IntegralCohomologicalAdicCriterion`
- `Sheaf.Paper.IntegralHomReduction`
- `Sheaf.Paper.IntegralLfpConstantModelComparison`
- `Sheaf.Topology.ProfiniteCondensedRing`
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`

The following nodes are no longer direct dependencies of the universe-transport proof.
They remain dependencies of the existing small-coefficient theorem where its source proof
uses them, so this delivery does not claim that they all leave the targets' import closure:

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-l-adic-extension-integers-dvr`
- `sk-prop-sfb-qlbar-colimit-x`
- `lem-sfb-integral-lfp-constant-model-comparison`
- `lem-sfb-integral-cohomological-adic-criterion`
- `lem-coef-integral-hom-reduction`
- `lem-sfb-finite-field-internal-hom-finiteness`
- `sk-thm-pe-constructible-comparison`
- `def-weil-pbc-locally-derived-ringed-ideal-complete`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `sk-def-sfb-derived-categories`
- `def-sfb-constructible-module`
- `def-weil-pbc-condensed-e-module-category`
- `sk-def-sfb-pullback-from-point`
- `sk-def-sfb-condensed-ring`
- `sk-def-sfb-qlbar-condensed`
- `def-sfb-locally-finitely-presented`
- `lem-weil-pbc-condensed-lfp-local-triviality`
- `lem-weil-pbc-condensed-qbar-lfp-local-triviality`
- `sk-def-sfb-constructible`
- `lem-sfb-dc-hom-scalar-adjunction`
- `lem-sfb-constructible-internal-hom-continuity`
- `lem-sfb-modobj-grothendieck`
- `def-sfb-rationalization-equivalence`
- `lem-sfb-extend-scalars-bounded-constructible`
- `sk-thm-sfb-qlbar-two-colimit`
- `lem-sfb-extend-subfield-constructible`
- `det-prop-sfb-cartesian-coefficients-finite-free`
- `lem-sfb-dc-hom-filtered-colimit`
- `lem-sfb-extend-to-qlbar-constructible`

Removed obsolete top-level tool-use approvals from the item's node: all ten entries
in its previous tool_uses list. Their mathematical uses remain in the unchanged source
argument attached to the small-coefficient dependency. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox tried to assert `IsEllAdicFinitenessCoefficient` directly for a
universe-generalized coefficient ring. The class has rigid Type 0 constructors; a
coefficient-ring isomorphism does not imply equality of the indexed objects. Those
unproved bridges are not delivered. The actual shorter route transports bounded
constructibility and the ambient internal Hom along a constructed isomorphism.
The unit's preservation step is retained; the existing finiteness theorem supplies it.

## New nodes

`lem-sfb-dc-hom-small-coefficients` attaches the already existing
`isMonoidalClosed_boundedConstructible` instance to its own dependency node, preserving
the former Bhatt–Scholze proof plan. It adds no Lean declaration and no sorry. This avoids
a self edge when the universe-generalized theorem invokes the existing class-indexed
instance previously discussed under the same item node.

Change record: `coord/changes/h5-bounded-constructible-hom-proof-scopes.md`
documents the private helper section and file-level opens flagged by the
static interface checker; public signatures and public imports are unchanged.

The proof uses `new-integral-residue-derived-monoidal` as a tool: its proved
`Functor.residueDerivedMonoidal` construction supplies strong monoidality
for the exact restriction-of-scalars equivalence. This generic construction
is recorded in another unit; no finiteness or preservation step of this unit
is bypassed. No tool-use approval is added by this delivery.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
