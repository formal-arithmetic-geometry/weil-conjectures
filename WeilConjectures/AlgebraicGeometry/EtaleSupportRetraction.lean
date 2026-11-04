/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSupportSequence
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
import WeilConjectures.Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Iso

/-!
# Low-degree support vanishing along a closed immersion with a retraction

If a closed immersion `i : Z ⟶ P` with open complement `j` has a retraction `p`, then the
right-derived sections with support in `Z` of an étale sheaf `M` vanish in degrees `< 2` as soon
as `p_*` turns `M ⟶ j_* j^* M` into an isomorphism and `R¹p_* M = 0`. This is the general step
of the standard-pair calculation of `lem-pur-smooth-divisor-low-support`.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Low-degree support vanishing along a closed immersion with a retraction.

Let `i : Z ⟶ P` be a closed immersion with open complement `j : U ⟶ P` and a retraction
`p : P ⟶ Z`. If the open restriction `M ⟶ j_* j^* M` becomes an isomorphism after `p_*` and
`R¹p_* M = 0`, then `RΓ_Z(M)` has no cohomology in degrees `< 2`.

Proof: take the chosen injective resolution `I` of `M`. The support sequence
`0 ⟶ i_* i^! I ⟶ I ⟶ j_* j^* I ⟶ 0` is short exact and termwise split, so it stays short
exact after `p_*`. Since `p_* i_* ≅ 𝟭`, its first term becomes `i^! I`. The long exact
homology sequence, the left exactness of `p_*` in degree `0` and `R¹p_* M = 0` kill the
homology of `i^! I` in degrees `0` and `1`; exactness of `i_*` transports this to
`RΓ_Z(M) = Γ_Z(I) ≅ i_* i^! I`. Negative degrees vanish since `M` sits in degree `0`. -/
theorem isZero_homology_rightDerived_sectionsWithSupport_of_retraction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (p : P ⟶ Z) (hip : i ≫ p = 𝟙 Z)
    (M : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h₀ : IsIso ((lowerStar (ModuleCat.{u + 1} A) p).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M)))
    (h₁ : IsZero (((lowerStar (ModuleCat.{u + 1} A) p).rightDerived 1).obj M))
    (q : ℤ) (hq : q < 2) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((sectionsWithSupport (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let C := ModuleCat.{u + 1} A
  let Γ := sectionsWithSupport C j
  let Sh := Sheaf P.smallEtaleTopology C
  rcases lt_or_ge q 0 with hq0 | hq0
  · have := Γ.isGE_rightDerivedFunctor_obj_singleFunctor M
    exact DerivedCategory.isZero_of_isGE _ 0 q hq0
  let R := injectiveResolution M
  let I := R.cochainComplex
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  obtain ⟨δ, -, hseq⟩ := etale_injective_support_sequence A i j hij
  obtain ⟨hS, -⟩ := hseq I (DerivedCategory.Q.obj I) (Iso.refl _)
  let S := etaleSupportSequence A i j hij I
  let F := lowerStar C p
  let T := S.map (F.mapHomologicalComplex (.up ℤ))
  let adj := upperStarLowerStarAdjunction C j
  have hT : T.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro r
    have hSr := hS.map_of_exact (HomologicalComplex.eval Sh (.up ℤ) r)
    have : IsSplitEpi (S.map (HomologicalComplex.eval Sh (.up ℤ) r)).g := by
      change IsSplitEpi ((adj.mapHomologicalComplex (.up ℤ)).unit.app I |>.f r)
      rw [Adjunction.mapHomologicalComplex_unit_app_f]
      exact isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective C j i hij (I.X r)
    have : Mono (S.map (HomologicalComplex.eval Sh (.up ℤ) r)).f := hSr.mono_f
    exact ((ShortComplex.Splitting.ofExactOfSection _ hSr.exact
      (section_ (S.map (HomologicalComplex.eval Sh (.up ℤ) r)).g) (IsSplitEpi.id _)
      this).map F).shortExact
  have hI : IsZero (I.X (-1)) := CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by norm_num)
  have h₃ : IsZero (T.X₃.homology (-1)) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      (F.map_isZero ((lowerStar C j).map_isZero ((upperStar C j).map_isZero hI)))
  have h₂ : IsZero (T.X₂.homology 1) :=
    h₁.of_iso (R.isoRightDerivedObjCochainComplex F 1).symm
  have hg : IsIso (HomologicalComplex.homologyMap T.g 0) := by
    have hM : IsZero (((CochainComplex.singleFunctor Sh 0).obj M).X (-1)) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by norm_num)
    have hι : IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map R.ι') 0) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      exact CochainComplex.quasiIsoAt_map_zero_of_preservesFiniteLimits F R.ι' hM hI
    have hjι : IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map
        (((upperStar C j).mapHomologicalComplex (.up ℤ) ⋙
          (lowerStar C j).mapHomologicalComplex (.up ℤ)).map R.ι')) 0) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      exact CochainComplex.quasiIsoAt_map_zero_of_preservesFiniteLimits
        (upperStar C j ⋙ lowerStar C j ⋙ F) R.ι' hM hI
    have hunit : IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor Sh 0).obj M))) 0) := by
      have (n : ℤ) : IsIso (((F.mapHomologicalComplex (.up ℤ)).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app
            ((CochainComplex.singleFunctor Sh 0).obj M))).f n) := by
        rw [Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_unit_app_f]
        by_cases hn : n = 0
        · subst hn
          exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight adj.unit F)
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M)).2 h₀
        · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn
          exact ⟨⟨0, (F.map_isZero hz).eq_of_src _ _,
            (F.map_isZero ((lowerStar C j).map_isZero
              ((upperStar C j).map_isZero hz))).eq_of_src _ _⟩⟩
      have := HomologicalComplex.Hom.isIso_of_components ((F.mapHomologicalComplex (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor Sh 0).obj M)))
      infer_instance
    have hsq := congrArg (fun φ ↦ HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map φ) 0)
      ((adj.mapHomologicalComplex (.up ℤ)).unit.naturality R.ι')
    simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp, Functor.id_map] at hsq
    have : IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map R.ι') 0 ≫
        HomologicalComplex.homologyMap T.g 0) := by
      erw [hsq]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map R.ι') 0) _
  obtain ⟨hz₀, hz₁⟩ := CochainComplex.isZero_homology_zero_one_of_shortExact hT h₃ h₂ hg
  let K := ((closedUpperShriek C i j).mapHomologicalComplex (.up ℤ)).obj I
  let e : lowerStar C i ⋙ F ≅ 𝟭 _ :=
    lowerStarComp C i p (𝟙 Z) hip.symm ≪≫ lowerStarId C Z
  let eK : T.X₁ ≅ K := (NatIso.mapHomologicalComplex e (.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app K
  have hK : IsZero (K.homology q) := by
    obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact hz₀.of_iso ((HomologicalComplex.homologyFunctor _ _ 0).mapIso eK.symm)
    · exact hz₁.of_iso ((HomologicalComplex.homologyFunctor _ _ 1).mapIso eK.symm)
  let eΓ : (DerivedCategory.homologyFunctor _ q).obj (Γ.rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) ≅ S.X₁.homology q :=
    (DerivedCategory.homologyFunctor _ q).mapIso (Γ.rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Sh 0).app M ≪≫
        asIso (DerivedCategory.Q.map R.ι')) ≪≫ Γ.rightDerivedFunctorObjQIso I) ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (HomologicalComplex.homologyFunctor _ _ q).mapIso
        ((NatIso.mapHomologicalComplex (closedUpperShriekCompLowerStarIso C i j hij)
          (.up ℤ)).app I).symm
  exact ((lowerStar C i).map_isZero hK).of_iso (eΓ ≪≫ (K.sc q).mapHomologyIso (lowerStar C i))

end AlgebraicGeometry.Etale
