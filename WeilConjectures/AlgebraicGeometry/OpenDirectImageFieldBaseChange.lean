/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothBaseChangeCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Base change for open direct images over a field

Source: blueprint sec-six-functors-basics/sk-cor-geo-open-finiteness,
`det-geo-open-finiteness-base-change.md`; Stacks Project, Tag 0D6J
(blueprint: det-geo-open-finiteness-base-change).

The two pullback squares describe `YT = Y ×_k T` and `XT = X ×_Y YT = X ×_k T`.
The exchange is the recorded module-coefficient derived base-change morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Base change for an open immersion of finite-type schemes over a field, and bounded
constructibility of the resulting direct image, with finite primary coefficients.
Source: blueprint sec-six-functors-basics/sk-cor-geo-open-finiteness,
`det-geo-open-finiteness-base-change.md`; Stacks Project, Tag 0D6J(3)
(blueprint: det-geo-open-finiteness-base-change).

The isomorphism is stated in the ambient derived category, in which the bounded-below
category is full. This is the same canonical exchange, restricted to bounded-below objects.
No separation, smoothness, nonemptiness, or Tor-amplitude assumption is imposed.

Proof: translate finite-constant constructibility to the source library's constructibility
predicate, and regard the bounded complex as an object of the bounded-below derived category.
The exponent $\ell^r$ annihilates $\Lambda$ and is invertible over $\operatorname{Spec}k$.
Apply the finite-coefficient generic-open theorem
`exists_hasConstructibleDirectImageBaseChangeOn` to each cohomology sheaf. Its proof already
performs the coefficient devissage of [thm-fin-deligne-generic-open]. Every nonempty open of
$\operatorname{Spec}k$ is the whole space, so each cohomology sheaf has constructible direct
image and satisfies the canonical base-change isomorphism after every Noetherian base change.
The scheme $T$ is Noetherian since it is of finite type over the field.

`HasDirectImageBaseChangeOnPlus.of_bounded` performs the finite truncation induction: the
property for cohomology sheaves is stable under shifts, distinguished triangles and
isomorphisms, and hence holds for the bounded complex. Evaluate it on the two given Cartesian
squares. Finally use the canonical comparison between bounded-below and unbounded derived
functors; `isIso_derivedBaseChangeMap_app_ι_obj_iff` compares the actual exchange morphisms.
Transport the bounded-constructible direct image across the comparison isomorphism, convert
constructibility back, and express boundedness as vanishing outside a finite interval.
-/
theorem isIso_derivedBaseChangeMap_openImmersion_field_and_isBoundedConstructible
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (r : ℕ) (hr : 1 ≤ r) (hΛ : (ℓ ^ r : Λ) = 0)
    {X Y T : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    {XT YT : Scheme.{u}} (gX : XT ⟶ X) (gY : YT ⟶ Y)
    (bT : YT ⟶ T) (jT : XT ⟶ YT)
    (hYT : IsPullback gY bT aY aT) (sq : IsPullback gX jT j gY)
    (K : DerivedCategoryModule Λ X)
    (hK : DerivedCategory.isBoundedConstructible Λ X K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ∧
      DerivedCategory.isBoundedConstructible Λ YT
        ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((gX)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have _ := hr
  have _ := hj
  have hKsource : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
    obtain ⟨hc, a, b, _, hv⟩ := hK
    refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).2
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩, fun i ↦ ?_⟩
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hKsource.1
  let Kp : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K, ⟨a, ha⟩⟩
  have : _root_.DerivedCategory.Plus.IsGE Kp a :=
    (_root_.DerivedCategory.Plus.isGE_ι_obj_iff Kp a).1 ha
  have : _root_.DerivedCategory.Plus.IsLE Kp b :=
    (_root_.DerivedCategory.Plus.isLE_ι_obj_iff Kp b).1 hb
  have hchar : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓ.symm).isUnit
  have hpow : IsUnit ((ℓ ^ r : ℕ) : k) := by
    simpa only [Nat.cast_pow] using hchar.pow r
  have hΛ' : ((ℓ ^ r : ℕ) : Λ) = 0 := by
    simpa only [Nat.cast_pow] using hΛ
  have : HasInvertibleExponent Λ (Spec (.of k)) := by
    refine ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos r, hΛ', ?_⟩
    simpa only [map_natCast] using hpow.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hproperty : HasDirectImageBaseChangeOnPlus Λ aY j Kp Set.univ := by
    apply HasDirectImageBaseChangeOnPlus.of_bounded Kp a b
    intro q
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj Kp) := hKsource.2 q
    obtain ⟨U, ⟨s, hs⟩, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn Λ
      (𝟙 (Spec (.of k))) aY j
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj Kp)
    apply (hasConstructibleDirectImageBaseChangeOn_iff aY j _ Set.univ).1
    apply h.mono
    intro x _
    rwa [Subsingleton.elim x s]
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := ⟨⟩
  obtain ⟨hbounded, hiso⟩ := hproperty T aT (Set.subset_univ _) YT XT gY bT gX jT hYT sq
  let e : (R((jT)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((gX)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      _root_.DerivedCategory.Plus.ι.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) jT).rightDerivedFunctorPlus.obj
          ((upperStar (ModuleCat.{u + 1} Λ) gX).mapDerivedCategoryPlus.obj Kp)) :=
    (R((jT)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ gX).app K) ≪≫
      ((lowerStar (ModuleCat.{u + 1} Λ) jT).rightDerivedFunctorPlusCompatibility.app
        ((upperStar (ModuleCat.{u + 1} Λ) gX).mapDerivedCategoryPlus.obj Kp)).symm
  have htarget := ObjectProperty.prop_of_iso _ e.symm hbounded
  obtain ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, hconstructible⟩ := htarget
  refine ⟨(isIso_derivedBaseChangeMap_app_ι_obj_iff
    (ModuleCat.{u + 1} Λ) sq.toCommSq Kp).2 hiso, ?_⟩
  refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hconstructible i), min c d, max c d, min_le_max, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ c).1 hc i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ d).1 hd i
      (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.Etale
