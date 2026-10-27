## What changed

Restored the recovered proof of
`AlgebraicGeometry.ProEtale.finiteOpenLocalizing` on the current module text,
following the explicit recovered-proof assignment. The statement is unchanged.
The finite discrete coefficient is admissible by the existing proved private
`finiteDiscreteCoefficient_admissible`. Applying
`openImmersionLowerShriek_localizing` gives preservation of the Dctf generators
and the localizing closure. Triangulatedness gives the triangle clause.

The old two `infer_instance` calls for coproduct preservation hit the current
20,000-heartbeat typeclass limit. The repaired proof obtains preservation
explicitly from `derivedOpenImmersionLowerShriekUpperStarAdjunction` and
`Adjunction.leftAdjoint_preservesColimits`, including all existing coproducts
indexed by `Type (u + 2)` and the empty diagram. Added the private proof import
`Mathlib.CategoryTheory.Adjunction.Limits`. Public imports, definitions,
instances, statement signatures and the existing compactification proof are
unchanged. The entire module compiles with `lcompile.py` in 22.5 seconds,
without diagnostics.

The current repository source and the quarantined source are the same text
apart from no changes relevant to this repair; the current source was copied,
not the preferred upstream file wholesale. The node's Lean attachment and its
remaining proof dependencies are preserved. No archive is deleted.

## Proved and sorry left

Closed one of the original three holes:
`AlgebraicGeometry.ProEtale.finiteOpenLocalizing`
(node `det-ctf-finite-proper-localizing`). No holes were added or split off.

Two existing holes remain, unchanged:

- `AlgebraicGeometry.ProEtale.finiteProperLocalizing`
  (node `det-ctf-finite-proper-localizing`).
- `AlgebraicGeometry.ProEtale.finiteProperLocalizing_baseChange`
  (node `det-ctf-finite-proper-localizing`).

`AlgebraicGeometry.ProEtale.finiteCompactificationLocalizing` retains its
complete composition proof and still depends on `finiteProperLocalizing`.
The restored open proof is a proof from the recorded open-localizing theorem,
not an axiom-free closure claim about every dependency of the project.

## No longer needed

The following private imports are unused by the current declarations and were
removed; compiling the resulting module verifies that they are unnecessary
for this repair and the retained compactification proof:

- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProperHeartContinuitySections`
- `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`
- `Sheaf.Paper.FiniteDiscreteCondensedRing`
- `Sheaf.Paper.FiniteDiscreteSchemeRing`
- `Sheaf.SixFunctors.UnboundedClassicalTruncation`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `WeilConjectures.Topology.DimensionSupremumLocalDimensions`

These are removed import edges, not withdrawals of those modules or their
nodes. Some are still needed by the mathematical plan for the two unchanged
proper-image holes, so their DAG dependencies remain intact. No node or module
is declared globally unneeded. The existing node proof step for open extension
already describes exactly the restored argument; no route change or new node
is needed.

## Where the brief, the DAG or earlier work was wrong

The recovered proof's mathematical route is valid with the current interface.
Only its final typeclass searches needed replacement by the explicit derived
adjunction's colimit-preservation result. The two other proper-image holes
were already present in the recovered preferred source and are not closed by
this recovered-proof repair.

Read the current five-step node plan and the recorded dependency declarations,
including the finite classical-localizing, classical-coproduct, classical
truncation and geometric fibre-bound interfaces. Their ordinary intrinsic
constant-ring presentations differ from this item's internal-module coefficient
presentation; no unchecked transport or extra hypothesis has been inserted.
LeanFinder, Loogle and the authorized grep search found no direct Mathlib match.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
