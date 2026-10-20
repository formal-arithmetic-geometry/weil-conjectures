/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.SixFunctors.Finite.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Detecting derived comparisons off a finite boundary

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-comparison.md`
(blueprint: lem-fin-finite-boundary-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A comparison is invertible if its open restriction and proper direct image are
invertible and the complementary closed subscheme is finite over the base.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-comparison.md`
(blueprint: lem-fin-finite-boundary-comparison).

Proof plan:
1. Forget module coefficients to abelian sheaves using
   `lem-weil-pbc-module-abelian-derived-direct-image-comparison` and
   `prop-weil-pbc-inverse-image-modules-exact`. Exact forgetting commutes with cohomology
   and reflects isomorphisms, hence so does its derived functor by
   `lem-weil-pbc-derived-plus-iso-on-cohomology`.
2. Take a distinguished cone triangle of the forgotten comparison. Exact inverse image
   and derived direct image are triangulated (`prop-weil-pbc-inverse-image-exact`,
   `lem-sf-exact-functor-derived-triangulated`,
   `lem-weil-pbc-derived-direct-image-triangulated`). The long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`) and the cohomology criterion show that the cone M
   has zero open restriction and zero derived direct image.
3. The closed immersion is finite (`lem-weil-pbc-closed-immersion-finite`), so its direct
   image is exact (`lemma-weil-pbc-finite-direct-image-exact`). Every cohomology sheaf of M
   is supported on Z, by `lemma-openclosed-stalk-upperstar`. Closed-image recovery and
   full faithfulness (`lem-kun-04ca`) identify its adjunction unit with an isomorphism.
   Exactness and the cohomology criterion therefore give M ≅ i_*i^*M.
4. Put N = i^*M. Derived pushforward composition
   (`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`), computed on bounded below
   K-injectives (`def-weil-pbc-direct-image`), gives R(bi)_*N = 0. Finite exactness gives
   (bi)_*H^n(N) = 0 for every n.
5. By `lemma-weil-pbc-finite-stalk-formula`, each stalk of H^n(N) is a retract of a zero
   finite product, hence zero. Geometric-stalk conservativity
   (`lemma-weil-pbc-geometric-stalk-conservative`) gives H^n(N) = 0, including empty fibres.
6. The cohomology criterion gives N = 0, then M = 0. The original cone triangle and its
   cohomology sequence make the forgotten comparison invertible. Reflection in step 1
   makes c invertible. Properness is retained although this argument does not need it. -/
theorem isIso_of_finite_boundary
    (Λ : Type (u + 1)) [CommRing Λ] {Y S G Z : Scheme.{u}}
    (b : Y ⟶ S) [IsProper b]
    (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomplement : Set.range i.base = (Set.range a.base)ᶜ) [IsFinite (i ≫ b)]
    {K L : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (c : K ⟶ L)
    (hopen : IsIso ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.map c))
    (hpush : IsIso ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).map c)) :
    IsIso c := by
  -- Work in the ambient derived category through its fully faithful inclusion.
  let A := ModuleCat.{u + 1} Λ
  have hopen' : IsIso ((upperStar A a).mapDerivedCategory.map
      (_root_.DerivedCategory.Plus.ι.map c)) := by
    exact (NatIso.isIso_map_iff
      (upperStar A a).mapDerivedCategoryPlusCompatibility c).mp
        (inferInstanceAs (IsIso (_root_.DerivedCategory.Plus.ι.map
          ((upperStar A a).mapDerivedCategoryPlus.map c))))
  have hpush' : IsIso ((lowerStar A b).rightDerivedFunctor.map
      (_root_.DerivedCategory.Plus.ι.map c)) := by
    exact (NatIso.isIso_map_iff
      (lowerStar A b).rightDerivedFunctorPlusCompatibility c).mp
        (inferInstanceAs (IsIso (_root_.DerivedCategory.Plus.ι.map
          ((rightDerivedLowerStarPlus A b).map c))))
  obtain ⟨M, f, g, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (_root_.DerivedCategory.Plus.ι.map c)
  have hopenM : Limits.IsZero ((upperStar A a).mapDerivedCategory.obj M) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((upperStar A a).mapDerivedCategory.map_distinguished _ hT)).mpr hopen'
  have hpushM : Limits.IsZero ((lowerStar A b).rightDerivedFunctor.obj M) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((lowerStar A b).rightDerivedFunctor.map_distinguished _ hT)).mpr hpush'
  -- The cone is supported on the closed complement, hence recovered from it.
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A a i hcomplement M
  have hunit : IsIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hw).mp
      ((openImmersionLowerShriek A a).mapDerivedCategory.map_isZero hopenM)
  let N := (upperStar A i).mapDerivedCategory.obj M
  let e : M ≅ (lowerStar A i).rightDerivedFunctor.obj N :=
    asIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M)
  let ecomp := Functor.rightDerivedFunctorCompIso' (lowerStar A i) (lowerStar A b)
    (lowerStarComp A i b)
  have hpushN : Limits.IsZero ((lowerStar A (i ≫ b)).rightDerivedFunctor.obj N) :=
    hpushM.of_iso (((lowerStar A b).rightDerivedFunctor.mapIso e) ≪≫ ecomp.app N).symm
  -- Finite exact pushforward detects zero on each cohomology sheaf.
  have hN : Limits.IsZero N := by
    apply (_root_.DerivedCategory.isZero_iff N).mpr
    intro n
    let en : (_root_.DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar A (i ≫ b)).rightDerivedFunctor.obj N) ≅
        (lowerStar A (i ≫ b)).obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj N) :=
      (_root_.DerivedCategory.homologyFunctor _ n).mapIso
          ((rightDerivedFunctorLowerStarIsoMapDerivedCategory A (i ≫ b)).app N) ≪≫
        ((lowerStar A (i ≫ b)).mapDerivedCategoryHomologyFunctorIso n).symm.app N
    exact isZero_of_isZero_lowerStar_of_isFinite A (i ≫ b)
      (((_root_.DerivedCategory.homologyFunctor _ n).map_isZero hpushN).of_iso en.symm)
  have hM : Limits.IsZero M :=
    (((lowerStar A i).rightDerivedFunctor).map_isZero hN).of_iso e
  have : IsIso (_root_.DerivedCategory.Plus.ι.map c) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp hM
  exact isIso_of_reflects_iso c _root_.DerivedCategory.Plus.ι

end AlgebraicGeometry.Etale
