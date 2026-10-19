# CategoryTheory.Adjunction.derivedCompositionAdjunctionNormalization

## Reason

Complete the normalized derived-composition proof with independent Hom universes.
The static gate treats its helper's section variables and local instance commands as
an interface change. Those commands are confined to a section ending before the
existing declarations. The helper is private and fully proved. Also prune unused
imports, including an unused public import of the general derived-adjunction module.
The original theorem signature and the real derivedCompositionLeftIso construction
remain byte-for-byte unchanged; no definition used by a target changes its meaning.

## Old

The original import block was:

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

There was no helper section. The existing normalization theorem had proof `by sorry`.

## New

The import block is now:

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
```

The added section starts with the following commands and introduces only the private,
proved `compIso_hom_eq_conjugate` lemma:

```lean
-- The proof of `rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`, with independent
-- Hom universes. The upstream statement fixes one common Hom universe.
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uB} {E : Type uA}
  [Category.{vC} C] [Category.{vB} D] [Category.{vA} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesKInjectiveComplexes]
  {L₁ : D ⥤ C} {L₂ : E ⥤ D} {L : E ⥤ C} [L₁.Additive] [L₂.Additive] [L.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj₁ : L₁ ⊣ F) (adj₂ : L₂ ⊣ G) (adj : L ⊣ H)
```

The local attributes cease at the section's `end`, before derivedCompositionLeftIso.
They do not export instances. The existing public signatures, visibility, universes
and definition body are unchanged. The ordinary and derived comparisons are the
specified conjugates; the representative equation follows by their canonical units.
No arbitrary data are chosen and no axiom or new sorry is introduced.

## Users

`tools/downstream.py` lists the following 62 transitive consumers. A separate
import-only scan agrees with that list. Ten directly import this module, all via
proof-only imports. Each direct importer is compiled unchanged against the pruned
module; hence removing the unused public import does not change a consumer's
statement or require an adaptation. For the remaining modules the same immediate
interfaces are preserved. Claims are not acquired or changed; their holders need
no adaptation request. No consumer file is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization | N3 | sole changed module; complete proof and private helper, unused imports removed |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.KunnethMapAgrees | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.OpenProductExchange | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.EtaleCohomology.KunnethOneProper | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.ExceptionalInverseImageExistence | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.FiniteForwardProductSymmetry | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.FiniteProductCompactification | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.KunBcKunnethCompat | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.ModelCompactComparisonUnit | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.NearbyCycleSheafFiniteness | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.NearbyProperHyperdescent | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.NearbySpecializationSlice | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.OrgogozoGoodModification | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.OrientedProperFibreExchange | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.OrientedProperImageConstructibility | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.ProperExceptionalRestriction | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Paper.TraitNearbyBaseChange | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionLine | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.SmoothPurity.NormalizedWitness | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Targets.PoincareUncurry | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.Targets.SmoothPurityQbar | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.BoundedConstructibleTransport | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence | not consulted; unchanged | no signature or definition change; no adaptation |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | not consulted; unchanged | no signature or definition change; no adaptation |
| TargetsCheck | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.PoincareDuality.Poincare | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.PoincareDuality.Verdier | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.SmoothPurity.Defs | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Basic | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Basic | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Correspondence | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Dualizing | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Frobenius | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Main | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Stalk | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.TraceFormula.Statement | not consulted; unchanged | no signature or definition change; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not consulted; unchanged | no signature or definition change; no adaptation |

No target statement or target-used definition changes, so target-statement review is
not reopened. The unit and its realized proof steps are preserved.

## Status

landed 20261019T005350-L-2758485 2026-10-19 (merge of deliver/N3/Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization)
