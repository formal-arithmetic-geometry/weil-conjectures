/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale

/-! # Cartesian Rees exchange for an arbitrary presentation of a pullback pair -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.SectionReesBaseChange

/-- The coefficientwise Rees map of a Cartesian square of smooth section pairs is
Cartesian over the affine lines. Source: sk-thm-dnc, Local construction, the formula
B[t,I/t] = B tensor_R[x] R[t,u] with x_i = t u_i, and arbitrary base change.
(blueprint: lem-sp-section-rees-cartesian-pair).
Proof: identify V' with the categorical pullback of g along b, by the given Cartesian
square. Its section is the canonical base-changed section, since both projections agree.
The coefficient maps of the extended Rees construction respect composition and these
isomorphisms. For the canonical pullback the centred etale charts give the displayed
polynomial presentation and its base-change tensor identity, with no flatness assumption
on b; away from the section the ideal is the unit ideal and the Rees space is punctured
product. The chart squares are pullbacks and cover V', so glue them. Equivalently transport
SectionReesBaseChange.base_change through the preceding pair isomorphism. The line map is
AffineSpace.map b because t is fixed by the coefficientwise Rees map. The empty base and
d = 0 use respectively an empty cover and the empty polynomial-variable set. -/
theorem pairMap_isPullback
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s) :
    IsPullback (pairMap s s' q b hsec) (Scheme.Hom.deformationSpaceProj g' s')
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b) := by
  classical
  let e := cart.isoPullback
  let s₀ := Scheme.Hom.baseChangeSection g s hs b
  have he : e.hom ≫ pullback.fst g b = q := cart.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd g b = g' := cart.isoPullback_hom_snd
  have : IsClosedImmersion s₀ := MorphismProperty.of_isPullback
    (Scheme.Hom.isPullback_baseChangeSection g s hs b).flip inferInstance
  have hs₀ : s' ≫ e.hom = s₀ := by
    apply pullback.hom_ext
    · dsimp only [s₀]
      rw [Category.assoc, he, Scheme.Hom.baseChangeSection_fst, hsec]
    · dsimp only [s₀]
      rw [Category.assoc, he₂, Scheme.Hom.baseChangeSection_snd, hs']
  have centres : IsPullback s' (𝟙 S') e.hom s₀ :=
    IsPullback.of_vert_isIso ⟨hs₀.trans (Category.id_comp _).symm⟩
  have hideal : s'.ker = s₀.ker.comap e.hom := by
    rw [← centres.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  let hJ : ∀ ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
      (hU : U'.1 ≤ q ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (q.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
    fun {U' U} hU ↦
      (s.ker.ideal_map_appLE_le_ideal_comap q ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s' s q b hsec).1 ⟨U'.1, U'.2⟩)
  apply Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
    q s.ker s'.ker hJ ?_ g g' b cart
  intro x
  obtain ⟨U₀, U, hU, hx, hle, H⟩ :=
    Scheme.Hom.exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d (e.hom x)
  let U' : V'.AffineZariskiSite := ⟨e.hom ⁻¹ᵁ U₀.1, U₀.2.preimage_of_isIso e.hom⟩
  have hU' : U'.1 ≤ q ⁻¹ᵁ U.1 := by
    intro y hy
    have hh : pullback.fst g b (e.hom y) ∈ U.1 := hU hy
    change q y ∈ U.1
    simpa only [← Scheme.Hom.comp_apply, he] using hh
  let a := (pullback.fst g b).appLE U.1 U₀.1 hU
  let a' := e.hom.appLE U₀.1 U'.1 le_rfl
  have ha' : IsIso a' := by
    simpa only [a', U', Scheme.Hom.appLE_eq_app] using
      (inferInstance : IsIso (e.hom.app U₀.1))
  have hI : (s₀.ker.siteIdeal U₀).map a'.hom = s'.ker.siteIdeal U' := by
    rw [hideal]
    exact (Scheme.IdealSheafData.ideal_comap_appLE s₀.ker e.hom
      ⟨U₀.1, U₀.2⟩ ⟨U'.1, U'.2⟩ le_rfl).symm
  let r := CommRingCat.ofHom ((s₀.ker.siteIdeal U₀).extendedReesAlgebraMap
    a'.hom (s'.ker.siteIdeal U') hI.le)
  have hr : IsIso r := (ConcreteCategory.isIso_iff_bijective _).mpr
    (Ideal.bijective_extendedReesAlgebraMap (asIso a').commRingCatIsoToRingEquiv _ hI)
  have H' : IsPushout a'
      (CommRingCat.ofHom (algebraMap _ (s₀.ker.siteIdeal U₀).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap _ (s'.ker.siteIdeal U').extendedReesAlgebra)) r :=
    IsPushout.of_horiz_isIso ⟨by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact (Ideal.extendedReesAlgebraMap_algebraMap a'.hom
        (s'.ker.siteIdeal U') hI.le z).symm⟩
  refine ⟨U', U, hU', hx, ?_⟩
  have hh := H.paste_horiz H'
  have haa : a ≫ a' = q.appLE U.1 U'.1 hU' := by
    dsimp only [a, a']
    simp only [Scheme.Hom.appLE_comp_appLE, he]
  simp only [Scheme.IdealSheafData.toReesPresheaf_app,
    Scheme.IdealSheafData.extendedReesPullbackData_map]
  have hrr : CommRingCat.ofHom ((s.ker.siteIdeal U).extendedReesAlgebraMap
      (q.appLE U.1 U'.1 hU').hom (s'.ker.siteIdeal U') (hJ hU')) =
      CommRingCat.ofHom ((s.ker.siteIdeal U).extendedReesAlgebraMap a.hom _ hle) ≫ r := by
    apply CommRingCat.hom_ext
    dsimp only [r, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [Ideal.extendedReesAlgebraMap_comp]
    have haa' := congrArg CommRingCat.Hom.hom haa
    change a'.hom.comp a.hom = _ at haa'
    simp only [haa']
  rw [hrr, ← haa]
  exact hh

end AlgebraicGeometry.SectionReesBaseChange
