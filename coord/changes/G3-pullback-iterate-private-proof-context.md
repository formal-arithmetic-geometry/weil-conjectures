# AlgebraicGeometry.Scheme.trf_pullback_coefficient_iterate_coherence

## Reason

The proof adds module-level transparency settings, local irreducibility attributes,
universe names for private categorical helpers, and section variables used only by
those helpers. The static preflight requires a change record for these commands.
This record documents their scope; it records no replacement of any public statement
or definition. All five existing public signatures, all three definition bodies,
and all seven public imports remain verbatim.

The two categories of the square are fixed in the private helpers. The functor families
are passed directly, without eta expansion, in the final application. This avoids
normalizing the termwise derived inverse-image construction while checking the generic
comparison calculation. All private helpers are proved; no data is chosen or changed.

The settings affect elaboration of this module. The attributes are explicitly local;
the additional variables are section variables of private theorems. An importing module
receives the same public operations and propositions. The five target declarations and
the meanings of their definitions are unchanged, so this requires no semantic repair.

## Old

The existing public theorem signature, verbatim:

```lean
theorem trf_pullback_coefficient_iterate_coherence (A : Type u) [CommRing A] [Finite A]
    {W X : Scheme.{u}} (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X)
    (w : tW ≫ h = h ≫ t) (K : proEtaleDerivedCategory X A) :
    (∀ m : ℕ,
      (trfPullbackSquareComparison A h ((End.of tW) ^ (m + 1))
        ((End.of t) ^ (m + 1)) (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (proEtaleConstantRingDerivedPullback A h).map ((trfPullbackPowerStep A t m).hom.app K) =
        (trfPullbackPowerStep A tW m).hom.app
            ((proEtaleConstantRingDerivedPullback A h).obj K) ≫
          (proEtaleConstantRingDerivedPullback A tW).map
            ((trfPullbackSquareComparison A h ((End.of tW) ^ m) ((End.of t) ^ m)
              (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (trfPullbackSquareComparison A h tW t w).hom.app
            ((proEtaleConstantRingDerivedPullback A ((End.of t) ^ m)).obj K)) ∧
      (∀ (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) (n : ℕ),
        trfCoefficientIterate A tW ((proEtaleConstantRingDerivedPullback A h).obj K)
            ((trfPullbackSquareComparison A h tW t w).hom.app K ≫
              (proEtaleConstantRingDerivedPullback A h).map f) n =
          (trfPullbackSquareComparison A h ((End.of tW) ^ (n + 1))
              ((End.of t) ^ (n + 1))
              (trf_commuting_endomorphism_powers h tW t w (n + 1))).hom.app K ≫
            (proEtaleConstantRingDerivedPullback A h).map (trfCoefficientIterate A t K f n))
```

The former surrounding commands, verbatim:

```lean
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme
```

## New

The public theorem signature is identical:

```lean
theorem trf_pullback_coefficient_iterate_coherence (A : Type u) [CommRing A] [Finite A]
    {W X : Scheme.{u}} (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X)
    (w : tW ≫ h = h ≫ t) (K : proEtaleDerivedCategory X A) :
    (∀ m : ℕ,
      (trfPullbackSquareComparison A h ((End.of tW) ^ (m + 1))
        ((End.of t) ^ (m + 1)) (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (proEtaleConstantRingDerivedPullback A h).map ((trfPullbackPowerStep A t m).hom.app K) =
        (trfPullbackPowerStep A tW m).hom.app
            ((proEtaleConstantRingDerivedPullback A h).obj K) ≫
          (proEtaleConstantRingDerivedPullback A tW).map
            ((trfPullbackSquareComparison A h ((End.of tW) ^ m) ((End.of t) ^ m)
              (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (trfPullbackSquareComparison A h tW t w).hom.app
            ((proEtaleConstantRingDerivedPullback A ((End.of t) ^ m)).obj K)) ∧
      (∀ (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) (n : ℕ),
        trfCoefficientIterate A tW ((proEtaleConstantRingDerivedPullback A h).obj K)
            ((trfPullbackSquareComparison A h tW t w).hom.app K ≫
              (proEtaleConstantRingDerivedPullback A h).map f) n =
          (trfPullbackSquareComparison A h ((End.of tW) ^ (n + 1))
              ((End.of t) ^ (n + 1))
              (trf_commuting_endomorphism_powers h tW t w (n + 1))).hom.app K ≫
            (proEtaleConstantRingDerivedPullback A h).map (trfCoefficientIterate A t K f n))
```

The new surrounding commands, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v v' u'

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Keep categorical calculations from unfolding the termwise derived-pullback construction.
set_option allowUnsafeReducibility true in
attribute [local irreducible] proEtaleConstantRingPullbackComposition
  proEtaleCanonicalPullbackComposition proEtaleConstantRingDerivedPullback
  proEtaleRingModuleAdjunctionNormalized proEtaleRingModuleUnitSection
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleConstantRingComparison proEtaleRingDirectImageMap
```

The remaining new `section`, `variable`, and `include` commands scope the proved private
helpers `assoc_reverse₂`, `power_cocycle₂`, `coefficient_zero₂`, and
`coherence_two_categories`. They introduce no public parameter or instance. The
`@[reassoc]` attributes generate only the associated private proof helpers. The public
theorem is proved from these calculations, the existing derived associativity theorem,
and the unchanged canonical comparison and recursion definitions.

## Users

`tools/downstream.py Sheaf.Paper.PullbackCoefficientIterateCoherence --uses
trfCoefficientIterate` and the same query for `trfPullbackSquareComparison` list the
item itself as the only textual user. Both queries list the following three transitive
consumers. They require no adaptation because no public signature or definition changes.
Current holders are taken from the shared claim records.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.PullbackCoefficientIterateCoherence` | G3 | Both holes proved; local proof context added. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Identical public interface and definition bodies; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Identical public interface and definition bodies; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Identical public interface and definition bodies; no adaptation. |

## Status

landed 20261020T211719-L-3491557 2026-10-20 (merge of deliver/G3/Sheaf.Paper.PullbackCoefficientIterateCoherence)
