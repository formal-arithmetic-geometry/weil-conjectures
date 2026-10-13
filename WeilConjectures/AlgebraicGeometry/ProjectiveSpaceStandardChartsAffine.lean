/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-!
# Standard charts and coordinate sections of projective space

Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts-part3).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The polynomial generator on the integral chart is the ratio of homogeneous coordinates. -/
private lemma projIntBasicOpenIso_appTop_X (n : Type u) (i : n)
    (j : {j : n // j ≠ i}) :
    (projIntBasicOpenIso n i).hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial {j : n // j ≠ i} (ULift.{u} ℤ)))).inv
        (MvPolynomial.X j)) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
        (MvPolynomial.X i)).topIso.inv
        (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1)) := by
  classical
  rw [projIntBasicOpenIso_hom, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv (Spec.map _).appTop,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp only [CommRingCat.hom_ofHom]
  rw [Proj.basicOpenIsoSpec_hom, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id_assoc, CommRingCat.comp_apply]
  congr 2
  change (MvPolynomial.homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) i).symm
    (MvPolynomial.X j) = MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1
  rw [MvPolynomial.homogeneousLocalizationAwayXEquiv_symm_X]
  rfl

/-- The relative affine-space coordinate pulls back to the integral coordinate ratio. -/
private lemma standardOpenIso_appTop_coord (n : Type u) (S : Scheme.{u}) (i : n)
    (j : {j : n // j ≠ i}) :
    (standardOpen n S i).topIso.hom
      ((standardOpenIso n S i).hom.appTop (AffineSpace.coord S j)) =
      (toProjInt n S).app
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
          (MvPolynomial.X i))
        (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1)) := by
  rw [show AffineSpace.coord S j =
    AffineSpace.toSpecMvPolyIntEquiv _ (AffineSpace.toSpecMvPoly _ S) j from rfl,
    ← AffineSpace.toSpecMvPolyIntEquiv_comp, standardOpenIso_hom_toSpecMvPoly,
    AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_apply,
    projIntBasicOpenIso_appTop_X]
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply]
  erw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  erw [← CommRingCat.comp_apply
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
      (MvPolynomial.X i)).topIso.inv
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
      (MvPolynomial.X i)).topIso.hom, Iso.inv_hom_id, CommRingCat.id_apply]
  simp only [standardOpen, Scheme.Hom.appLE_eq_app]
  rfl

/-- Over an affine base open, a standard chart has the polynomial coordinate ring,
with the indicated coefficient and coordinate maps.
Source: Stacks Project, Constructions, Tag 01NG; Schemes, Tags 01JR and 01I4.
(blueprint: lem-weil-pbc-projective-space-standard-charts-part3).

Proof: Put W = D_+(T_i)_S ∩ q⁻¹(V). Restrict the defining pullback square of projective
space to V and to the integral standard chart D_+(T_i). The open-fibre-product formula
identifies W with V ×_{Spec Z} D_+(T_i), with its maps to V and the integral chart.
The integral chart is Spec Z[U_j : j ≠ i], with U_j = T_j/T_i, by projIntBasicOpenIso.
Using eV and pullbackSpecIso identifies W with Spec (R ⊗_Z Z[U_j]). The polynomial
scalar-extension equivalence sends r ⊗ 1 to C r and 1 ⊗ U_j to X j and identifies this
ring with R[U_j]. Thus W is affine. Take h to be the projection of the restricted
pullback square to V, so h followed by V.ι is W.ι followed by q. Global sections of the
constructed scheme isomorphism give E. Compatibility of pullbackSpecIso with its two
projections, followed by the scalar-extension formulas, identifies E(C r) with the
map of h followed by eV.hom and E(X j) with the restriction of rho-sharp(T_j/T_i).
The topIso in the coefficient formula is exactly the identification of sections on W
with global sections of W.toScheme. This proves every displayed compatibility. -/
theorem projectiveSpace_standardCharts_part3 (n : Type u) (S : Scheme.{u})
    [Finite n] [Nonempty n] :
    ∀ (V : S.Opens) (R : CommRingCat.{u}) (eV : V.toScheme ≅ Spec R) (i : n),
      IsAffineOpen (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V) ∧
      ∃ (h : (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).toScheme ⟶ V.toScheme)
        (E : MvPolynomial {j : n // j ≠ i} R ≃+*
          Γ(ℙ(n; S), standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V)),
        h ≫ V.ι = (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).ι ≫ (ℙ(n; S) ↘ S) ∧
        (∀ r : R, E (MvPolynomial.C r) =
          (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).topIso.hom
            ((h ≫ eV.hom).appTop ((Scheme.ΓSpecIso R).inv r))) ∧
        ∀ j : {j : n // j ≠ i}, E (MvPolynomial.X j) =
          (ℙ(n; S)).presheaf.map (homOfLE
            (inf_le_left : standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V ≤ standardOpen n S i)).op
          ((toProjInt n S).app
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
            (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1))) := by
  intro V R eV i
  let W := standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V
  let h := (ℙ(n; S) ↘ S).resLE V W inf_le_right
  let a := (ℙ(n; S)).homOfLE (inf_le_left : W ≤ standardOpen n S i)
  have hp : IsPullback a h ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S) V.ι := by
    have hp := (isPullback_opens_inf (standardOpen n S i)
      ((ℙ(n; S) ↘ S) ⁻¹ᵁ V)).paste_vert
        (isPullback_morphismRestrict (ℙ(n; S) ↘ S) V).flip
    simpa [a, h, Scheme.Hom.resLE] using hp
  let k := a ≫ (standardOpenIso n S i).hom
  have hp' : IsPullback k h (𝔸({j : n // j ≠ i}; S) ↘ S) V.ι := by
    exact hp.of_iso (Iso.refl _) (standardOpenIso n S i) (Iso.refl _) (Iso.refl _)
      (by simp [k]) (by simp) (by simp) (by simp)
  -- Both squares are pullbacks of the affine-space projection along the open immersion V.ι.
  let e := hp'.isoIsPullback _ _ (AffineSpace.isPullback_map V.ι)
  have hV : IsAffine V.toScheme := .of_isIso eV.hom
  have hW : IsAffine W.toScheme := .of_isIso e.hom
  refine ⟨hW, ?_⟩
  let c : R →+* Γ(ℙ(n; S), W) := W.topIso.hom.hom.comp
    ((h ≫ eV.hom).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
  let x : {j : n // j ≠ i} → Γ(ℙ(n; S), W) := fun j ↦
    (ℙ(n; S)).presheaf.map (homOfLE (inf_le_left : W ≤ standardOpen n S i)).op
      ((toProjInt n S).app
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
          (MvPolynomial.X i))
        (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1)))
  let f := MvPolynomial.eval₂Hom c x
  let eA : 𝔸({j : n // j ≠ i}; V.toScheme) ≅ 𝔸({j : n // j ≠ i}; Spec R) :=
    ⟨AffineSpace.map _ eV.hom, AffineSpace.map _ eV.inv,
      by rw [← AffineSpace.map_comp, eV.hom_inv_id, AffineSpace.map_id],
      by rw [← AffineSpace.map_comp, eV.inv_hom_id, AffineSpace.map_id]⟩
  let d := e ≪≫ eA ≪≫ AffineSpace.SpecIso {j : n // j ≠ i} R
  -- Global sections of the constructed spectrum isomorphism give a bijective ring map.
  let F : MvPolynomial {j : n // j ≠ i} R →+* Γ(ℙ(n; S), W) :=
    W.topIso.hom.hom.comp
      (d.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (MvPolynomial {j : n // j ≠ i} R))).inv.hom)
  have hF : Function.Bijective F :=
    (ConcreteCategory.bijective_of_isIso W.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso d.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
  have hcoeff : ∀ r : R, F (MvPolynomial.C r) = c r := by
    intro r
    change ((Scheme.ΓSpecIso (.of (MvPolynomial {j : n // j ≠ i} R))).inv ≫
      d.hom.appTop ≫ W.topIso.hom) (MvPolynomial.C r) = _
    simp only [d, Iso.trans_hom, Scheme.Hom.comp_appTop,
      AffineSpace.SpecIso_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply]
    simp only [CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      CommRingCat.comp_apply]
    change W.topIso.hom (e.hom.appTop ((AffineSpace.map _ eV.hom).appTop
      ((𝔸({j : n // j ≠ i}; Spec R) ↘ Spec R).appTop
        ((Scheme.ΓSpecIso R).inv r)))) = _
    have hebase : e.hom ≫ AffineSpace.map {j : n // j ≠ i} eV.hom ≫
        (𝔸({j : n // j ≠ i}; Spec R) ↘ Spec R) = h ≫ eV.hom := by
      rw [AffineSpace.map_over, ← Category.assoc]
      simp [e]
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, c, RingHom.comp_apply]
      using congrArg (fun m ↦ W.topIso.hom (m.appTop ((Scheme.ΓSpecIso R).inv r))) hebase
  have hcoord : ∀ j : {j : n // j ≠ i}, F (MvPolynomial.X j) = x j := by
    intro j
    change ((Scheme.ΓSpecIso (.of (MvPolynomial {j : n // j ≠ i} R))).inv ≫
      d.hom.appTop ≫ W.topIso.hom) (MvPolynomial.X j) = _
    simp only [d, Iso.trans_hom, Scheme.Hom.comp_appTop,
      AffineSpace.SpecIso_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply]
    simp only [CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    change W.topIso.hom (e.hom.appTop ((AffineSpace.map _ eV.hom).appTop
      (AffineSpace.coord (Spec R) j))) = x j
    rw [AffineSpace.map_appTop_coord]
    have hecoord : e.hom.appTop (AffineSpace.coord V.toScheme j) =
        k.appTop (AffineSpace.coord S j) := by
      have he := congrArg (fun m ↦ m.appTop (AffineSpace.coord S j))
        (hp'.isoIsPullback_hom_fst _ _ (AffineSpace.isPullback_map V.ι))
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.map_appTop_coord] using he
    rw [hecoord]
    dsimp only [k]
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have hs := congrArg (fun z ↦ (standardOpen n S i).topIso.inv z)
      (standardOpenIso_appTop_coord n S i j)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hs
    rw [hs]
    change W.topIso.hom (((ℙ(n; S)).homOfLE inf_le_left).appTop _) = _
    rw [Scheme.homOfLE_appTop_topIso_inv]
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  -- Coefficients and variables determine the polynomial ring map.
  have hFf : F = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [f] using hcoeff r
    · intro j
      simpa [f] using hcoord j
  have hf : Function.Bijective f := hFf ▸ hF
  refine ⟨h, RingEquiv.ofBijective f hf, ?_, ?_, ?_⟩
  · exact Scheme.Hom.resLE_comp_ι _ _
  · intro r
    exact MvPolynomial.eval₂_C _ _ _
  · intro j
    exact MvPolynomial.eval₂_X _ _ _

end
end AlgebraicGeometry.ProjectiveSpace
