# SheafOfModules.FiniteFreeResolution private scalar-action proof context

## Reason

The main theorem's matrix clause needs the explicit tensor unit on sections.
Temporarily restore local semireducibility of the existing monoidal structure
while elaborating two private proved helpers, then restore its original local
irreducibility before the rest of the file. Respect transparency locally inside
the main theorem proof, retaining the original context for its signature and
corollaries. No exported attribute, signature,
public import, or existing definition body changes. All new helpers are private
and fully proved. No consumer requires adaptation or a statement review.

## Old

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
```

This existing attribute remains at its original location. There was no scalar-action
helper block between finiteFree_flat and the generic signed-interchange proof.

## New

The new private helper block additionally uses these local commands:

```lean
set_option allowUnsafeReducibility true in
attribute [local semireducible] SheafOfModules.monoidalCategory
-- private unit_action and tensor_matrix proofs
attribute [local irreducible] SheafOfModules.monoidalCategory
-- scoped inside the main proof only
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- main proof tactics
```

The private scalar definition is the existing section action, wrapped as a sheaf morphism:

```lean
private def scalar (F : Modules R) (s : Sections R) : F ⟶ F :=
  ⟨PresheafOfModules.sectionsSMul F.val s⟩
```

Its data is explicitly constructed, not chosen from an existence theorem.
The helper lemmas prove naturality, compatibility with sheafification and tensor,
and the finite-coordinate matrix identity. The private genericTransportIso explicitly
constructs the transported complex isomorphism from its component isomorphisms; it
keeps that proof abstract to avoid unfolding the localized sheaf tensor. They do not appear in any public type
or public definition body.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FiniteFreeResolutionTensor --uses
SheafOfModules.FiniteFreeResolution.tensor_matrix` reports 57 downstream modules
and no existing uses of the new private helper. Each consumer retains exactly its
existing statements and definitions. Current claim records give the holders below.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor` | H9 | Public interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | W6 | Public interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | J6 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ContinuousAlgClOpenFiniteness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | U4 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalTowerTrace` | E7 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteModelSheafQuotientConstructible` | X7 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteScalarLocalModelComplete` | X9 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.GeneralLfpAdicInputWitness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralAdicInputNormalization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstantModelHeart` | Z8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstructibleHeart` | F5 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralGeneralLfpHomFiniteness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartLocalModel` | Z9 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralModels` | J8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralTensorPullback` | H4 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ProperHeartBoundLattice` | G8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.RationalLocalizedHom` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.RationalTatePullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | Q3 | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Public interface unchanged; no adaptation required. |

## Status

landed 20261023T231526-L-3613348 2026-10-23 (merge of deliver/H9/Sheaf.Algebra.Homology.FiniteFreeResolutionTensor)
