## What changed

Filled eight existing helper proofs, without changing a declaration signature, definition,
public import, or target statement. The coefficient map is the unique lift of its finite
projection cone. Ordinary module pullback exists by the independent-universe pullback API.
For the bounded scalar model, projectivity gives algebraic flatness; a proved private
local-relation argument shows flatness of constants. The independent-universe bounded-flat
and change-of-rings results then give K-flatness and flat terms. The tower proofs use
consecutive-arrow naturality and the normalized tensor-unit formulas.

Private proved helpers handle coefficient-map naturality, flat constants, and compatibility
of quotient units, together with the abstract product-cone equation. Local irreducibility annotations keep elaboration from expanding selected
completion and scalar-extension constructions. The existing DAG node records the actual
helper proofs and retains the plans for the two unproved declarations. A source comparison
confirms that all 53 original non-theorem declarations and all public imports are unchanged.
Import-direction checks pass for each new Sheaf proof import, and the node proof dependencies
agree with its proof-step references. The complete delivered module compiles through
`lcompile.py` without warnings (51.4 seconds).

## Proved and sorry left

Eight of the ten original holes are closed, by declaration name in namespace
`WeilConjectures.CompletedPerfectScalar`:

- `constantUnit_local`
- `constant_additive`
- `directMap_existsUnique`
- `ordinaryPush_isRightAdjoint`
- `model_good`
- `quotientTowerIso_naturality`
- `reductionTowerMap_condition`
- `limitUnit_condition`

The two original holes remaining, each with its existing source and complete proof plan,
are `WeilConjectures.CompletedPerfectScalar.modelModules_exact` and
`WeilConjectures.CompletedPerfectScalar.completedPerfectScalarPullback`.
No holes were added or split off. This is a partial proof delivery, not a proof of the
final comparison package. In particular, it makes no claim that the main theorem is
axiom-free; its two retained holes remain visible.

## No longer needed

For `model_good`, finite-free splitting and the specialized bounded-above flat-site lemma
are replaced by flatness of projective modules, the local equational criterion, and the
independent-coefficient bounded-flat/change-of-rings APIs. The node
`lem-pc-bounded-above-flat-kflat-site` is removed from this node's proof dependencies.
No module is withdrawn, and no claim is made that a module becomes globally unreachable.

Removed unused private imports from this file:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Mathlib.Algebra.Module.Projective`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.AdicPerfectModelCompleteReduction`
- `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`
- `Sheaf.Paper.FinitePerfectAdicCoefficientLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`

Apart from the superseded bounded-flat dependency, the mathematical results among these
imports retain their planned roles in the two remaining proofs. Removing their unused
imports here is not a request to withdraw their nodes or modules.

The local command changes are documented in
`coord/changes/B4-completed-perfect-scalar-proof-environment.md`. The downstream check
found zero Lean consumers, and no target definition or statement is changed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The specialized bounded-flat API does not directly match
this module's independent scheme and coefficient universes. The existing independent-
coefficient API supplies the needed result. Likewise, the ordinary module-pullback
existence theorem already handles these universes, so no new existence lemma is needed.
The documented finite-summand argument for `model_good` is correct but unnecessary:
projectivity alone supplies flatness before constant realization and scalar extension.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
