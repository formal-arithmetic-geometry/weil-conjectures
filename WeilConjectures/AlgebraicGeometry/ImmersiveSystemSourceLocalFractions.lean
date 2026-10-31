/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.MvPolynomial.CommRing
import WeilConjectures.AlgebraicGeometry.CompleteLinearSystemClosed
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Local fractions in the ratios of an immersive generating system

Source: the finite-cover Bertini proof, paragraph 3; Stacks Tags 01NE and 01NF.
(blueprint: lem-zl-immersive-system-source-local-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem chart_polynomial_surjective
    (k : Type u) [Field k] (I : Type u) (i : I) :
    Function.Surjective
      (MvPolynomial.eval₂Hom
        (((ℙ(I; Spec (.of k)) ↘ Spec (.of k)).appLE ⊤
          (ProjectiveSpace.standardOpen I (Spec (.of k)) i) le_top).hom.comp
            (Scheme.ΓSpecIso (.of k)).inv.hom)
        (ProjectiveSpace.coordRatio I (Spec (.of k)) i)) := by
  let P := ℙ(I; Spec (.of k))
  let W := ProjectiveSpace.standardOpen I (Spec (.of k)) i
  let b : Γ(Spec (.of k), ⊤) →+* Γ(P, W) :=
    (P ↘ Spec (.of k)).appLE ⊤ W le_top |>.hom
  let E := MvPolynomial.eval₂Hom (b.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    (ProjectiveSpace.coordRatio I (Spec (.of k)) i)
  have hle : Subring.closure (Set.range b ∪
      Set.range (ProjectiveSpace.coordRatio I (Spec (.of k)) i)) ≤ E.range := by
    apply Subring.closure_le.mpr
    rintro a (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨MvPolynomial.C ((Scheme.ΓSpecIso (.of k)).hom a), ?_⟩
      simp [E]
    · exact ⟨MvPolynomial.X j, by simp [E]⟩
  have hc := ProjectiveSpace.closure_range_appLE_union_range_coordRatio
    (Spec (.of k)) i
  change Subring.closure (Set.range b ∪ _) = ⊤ at hc
  rw [hc] at hle
  intro a
  exact hle (Subring.mem_top a)

private theorem affine_stalk_fractions
    {Z Y : Scheme.{u}} (f : Y ⟶ Z) [SurjectiveOnStalks f]
    (W : Z.Opens) (hW : IsAffineOpen W) (y : Y) (hy : f y ∈ W)
    {A : Type u} [CommRing A] (E : A →+* Γ(Z, W)) (hE : Function.Surjective E)
    (a : Y.presheaf.stalk y) :
    ∃ p q : A,
      IsUnit (f.stalkMap y (Z.presheaf.germ W (f y) hy (E q))) ∧
      a * f.stalkMap y (Z.presheaf.germ W (f y) hy (E q)) =
        f.stalkMap y (Z.presheaf.germ W (f y) hy (E p)) := by
  let z : W := ⟨f y, hy⟩
  let := TopCat.Presheaf.algebra_section_stalk Z.presheaf z
  let := hW.isLocalization_stalk z
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective y a
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
    (hW.primeIdealOf z).asIdeal.primeCompl b
  obtain ⟨p', rfl⟩ := hE p
  obtain ⟨q', hq'⟩ := hE q.val
  refine ⟨p', q', ?_, ?_⟩
  · rw [hq']
    exact (IsLocalization.map_units (Z.presheaf.stalk (f y)) q).map (f.stalkMap y).hom
  · change b * Z.presheaf.germ W (f y) hy q.val =
      Z.presheaf.germ W (f y) hy (E p') at hpq
    have h := congrArg (f.stalkMap y) hpq
    simpa only [TopCat.Presheaf.stalk_open_algebraMap, CommRingCat.hom_comp,
      RingHom.map_mul, hq'] using h

open Scheme.Modules ProjectiveSpace in
private theorem generatingSections_local_fractions
    (k : Type u) [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (I : Type u) [Finite I] (M : Y.Modules) [M.IsInvertible]
    (s : I → M.sections) (hs : Epi (M.freeHomEquiv.symm s))
    [IsImmersion (homOfGeneratingSections I g M s hs)]
    (y : Y) (U : Y.Opens) (hy : y ∈ U) (e : Γ(M, U)) (he : IsFreeGenerator e) :
    let ρ : k →+* Y.presheaf.stalk y :=
      ((Y.presheaf.germ ⊤ y trivial).hom.comp g.appTop.hom).comp
        (Scheme.ΓSpecIso (.of k)).inv.hom
    let c : I → Y.presheaf.stalk y := fun j ↦ Y.presheaf.germ U y hy
      (he.coeff (M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤))))
    ∃ (i : I) (u : (Y.presheaf.stalk y)ˣ), (u : Y.presheaf.stalk y) = c i ∧
      ∀ a : Y.presheaf.stalk y, ∃ p q : MvPolynomial I k,
        IsUnit (MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : Y.presheaf.stalk y) * c j) q) ∧
        a * MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : Y.presheaf.stalk y) * c j) q =
          MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : Y.presheaf.stalk y) * c j) p := by
  classical
  dsimp only
  let φ := homOfGeneratingSections I g M s hs
  let P := ℙ(I; Spec (.of k))
  obtain ⟨ε, hε⟩ := generatingSections_pair g M s hs
  have hcover : φ y ∈ ⨆ i, standardOpen I (Spec (.of k)) i := by
    rw [iSup_standardOpen]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  let W := standardOpen I (Spec (.of k)) i
  let V := U ⊓ φ ⁻¹ᵁ W
  have hyV : y ∈ V := ⟨hy, hi⟩
  let t : I → Γ(M, V) := fun j ↦
    M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤))
  let eV : Γ(M, V) := M.presheaf.map (homOfLE inf_le_left).op e
  have heV : IsFreeGenerator eV := he.map inf_le_left
  have hsi : IsFreeGenerator (t i) := by
    simpa only [t, presheaf_map_homOfLE_map_homOfLE] using
      (isFreeGenerator_of_twistRestrict_iso ε.hom hε i).map
        (inf_le_right : V ≤ φ ⁻¹ᵁ W)
  obtain ⟨v, hv⟩ := heV.exists_unit_smul_eq hsi
  let u : (Y.presheaf.stalk y)ˣ := Units.map (Y.presheaf.germ V y hyV).hom v
  have hc (j : I) :
      Y.presheaf.germ U y hy
        (he.coeff (M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤)))) =
      Y.presheaf.germ V y hyV (heV.coeff (t j)) := by
    rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left) y hyV,
      ← he.coeff_map]
    simp only [presheaf_map_homOfLE_map_homOfLE]
    rfl
  have hui : (u : Y.presheaf.stalk y) = Y.presheaf.germ U y hy
      (he.coeff (M.presheaf.map (homOfLE le_top).op ((s i).val (Opposite.op ⊤)))) := by
    rw [hc, hv, heV.coeff_smul_self]
    rfl
  have hratio (j : I) :
      φ.stalkMap y (P.presheaf.germ W (φ y) hi (coordRatio I (Spec (.of k)) i j)) =
        (↑u⁻¹ : Y.presheaf.stalk y) * Y.presheaf.germ U y hy
          (he.coeff (M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤)))) := by
    have ht : t j = Y.presheaf.map (homOfLE inf_le_right).op
        (φ.app W (coordRatio I (Spec (.of k)) i j)) • t i :=
      presheaf_map_homOfLE_eq_smul (le_top : φ ⁻¹ᵁ W ≤ ⊤)
        (inf_le_right : V ≤ φ ⁻¹ᵁ W)
        (map_eq_coordRatio_smul_of_twistRestrict_iso ε.hom hε i j)
    have heq := congrArg heV.coeff ht
    rw [heV.coeff_smul_left, hv, heV.coeff_smul_self] at heq
    have hg := congrArg (Y.presheaf.germ V y hyV) heq
    rw [map_mul, Y.presheaf.germ_res_apply] at hg
    rw [Scheme.Hom.germ_stalkMap_apply, hc]
    rw [hg]
    change _ = (↑u⁻¹ : Y.presheaf.stalk y) * (_ * (u : Y.presheaf.stalk y))
    simp only [mul_left_comm (↑u⁻¹ : Y.presheaf.stalk y), Units.inv_mul, mul_one]
  refine ⟨i, u, hui, ?_⟩
  intro a
  let b := ((P ↘ Spec (.of k)).appLE ⊤ W le_top).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := MvPolynomial.eval₂Hom b (coordRatio I (Spec (.of k)) i)
  obtain ⟨p, q, hq, hpq⟩ := affine_stalk_fractions φ W
    (isAffineOpen_standardOpen I (Spec (.of k)) i) y hi E
    (chart_polynomial_surjective k I i) a
  have hE : (φ.stalkMap y).hom.comp ((P.presheaf.germ W (φ y) hi).hom.comp E) =
      MvPolynomial.eval₂Hom
        (((Y.presheaf.germ ⊤ y trivial).hom.comp g.appTop.hom).comp
          (Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun j ↦ (↑u⁻¹ : Y.presheaf.stalk y) * Y.presheaf.germ U y hy
          (he.coeff (M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤))))) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      rw [MvPolynomial.eval₂Hom_C]
      change φ.stalkMap y (P.presheaf.germ W (φ y) hi (E (MvPolynomial.C z))) =
        Y.presheaf.germ ⊤ y trivial (g.appTop ((Scheme.ΓSpecIso (.of k)).inv z))
      rw [show E (MvPolynomial.C z) = b z from MvPolynomial.eval₂Hom_C _ _ _]
      change φ.stalkMap y (P.presheaf.germ W (φ y) hi
        (P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((P ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv z)))) = _
      rw [P.presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply]
      change Y.presheaf.germ ⊤ y trivial
        (φ.appTop ((P ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv z))) = _
      apply congrArg (Y.presheaf.germ ⊤ y trivial)
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      rw [(homOfGeneratingSections_spec I g M s hs).1]
    · intro j
      change φ.stalkMap y (P.presheaf.germ W (φ y) hi
        (E (MvPolynomial.X j))) = _
      simpa only [E, MvPolynomial.eval₂Hom_X'] using hratio j
  have hEp (z : MvPolynomial I k) :
      φ.stalkMap y (P.presheaf.germ W (φ y) hi (E z)) =
        MvPolynomial.eval₂Hom
          (((Y.presheaf.germ ⊤ y trivial).hom.comp g.appTop.hom).comp
            (Scheme.ΓSpecIso (.of k)).inv.hom)
          (fun j ↦ (↑u⁻¹ : Y.presheaf.stalk y) * Y.presheaf.germ U y hy
            (he.coeff (M.presheaf.map (homOfLE le_top).op ((s j).val (Opposite.op ⊤))))) z :=
    DFunLike.congr_fun hE z
  exact ⟨p, q, (hEp q) ▸ hq, by rwa [hEp, hEp] at hpq⟩

/-- The source local ring of an immersion is generated by localized coordinate ratios.
No rationality, closed-point, or finite-type assumption is needed.

Source: latest blueprint,
`sk-lem-wgen-bertini-cover/lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Tags 01NE and 01NF and the affine description of an immersion.
(blueprint: lem-zl-immersive-system-source-local-fractions).

Proof: View x as a point of U₀. Since the sections generate the invertible module,
some s_i has nonzero image in its one-dimensional residue fibre. In the frame e,
its coefficient germ is therefore a unit u. The section-preserving isomorphism
classifying homOfGeneratingSections identifies the inverse image of the i-th standard
chart with the nonvanishing locus of s_i, and identifies the pulled-back coordinates
T_j/T_i with u⁻¹ times the coefficient germs of s_j. The chart over Spec k is affine
space, with coordinate ring the polynomial ring in T_j/T_i for j ≠ i. Its stalk is
the localization of that ring at the prime of the image of x. An immersion induces
a surjection from this stalk to the source stalk. The open inclusion U₀ → X identifies
the source stalk with O_(X,x). Thus any a is the image of a polynomial fraction p/q;
the denominator avoids the image prime, so its image is a unit. Multiply by this
denominator to get the displayed equality. Using all r variables adds the redundant
coordinate T_i/T_i = 1, which does not change surjectivity. No point exists when the
coordinate set is empty, since the empty family cannot generate an invertible stalk. -/
theorem immersiveSystem_source_local_fractions
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (U₀ : X.Opens) (L : X.Modules) [L.IsInvertible]
    (r : ℕ) (s : Fin r → Γ(L, ⊤))
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (s i.down))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (s i.down)))) hgen)]
    (x : X) (hxU₀ : x ∈ U₀)
    (U : X.Opens) (hxU : x ∈ U) (e : Γ(L, U))
    (he : Scheme.Modules.IsFreeGenerator e) :
    let ρ : k →+* X.presheaf.stalk x :=
      ((X.presheaf.germ ⊤ x trivial).hom.comp (X ↘ Spec (.of k)).appTop.hom).comp
        (Scheme.ΓSpecIso (.of k)).inv.hom
    let c : Fin r → X.presheaf.stalk x := fun j ↦
      X.presheaf.germ U x hxU
        (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s j)))
    ∃ (i : Fin r) (u : (X.presheaf.stalk x)ˣ), (u : X.presheaf.stalk x) = c i ∧
      ∀ a : X.presheaf.stalk x, ∃ p q : MvPolynomial (Fin r) k,
        IsUnit (MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : X.presheaf.stalk x) * c j) q) ∧
        a * MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : X.presheaf.stalk x) * c j) q =
          MvPolynomial.eval₂Hom ρ (fun j ↦ (↑u⁻¹ : X.presheaf.stalk x) * c j) p := by
  classical
  dsimp only
  let j := U₀.ι
  let y : U₀.toScheme := ⟨x, hxU₀⟩
  let M := (Scheme.Modules.tensorPullback j).obj L
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)
  let ε := (adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction j)).app L
  have : M.IsInvertible := Scheme.Modules.IsInvertible.of_iso ε.symm
  let η := adj.unit.app L
  let e' : Γ(M, j ⁻¹ᵁ U) := η.app U e
  have hε (V : X.Opens) (t : Γ(L, V)) :
      ε.hom.app (j ⁻¹ᵁ V) (η.app V t) = Scheme.Modules.pullbackSection j t := by
    exact congrArg (fun h ↦ h.app V t)
      (adj.unit_leftAdjointUniq_hom_app
        (Scheme.Modules.pullbackPushforwardAdjunction j) L)
  have he' : Scheme.Modules.IsFreeGenerator e' := by
    have h := (he.pullback_unit_app j).app_hom ε.symm
    have heq : ε.inv.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackSection j e) = e' := by
      rw [← hε U e]
      change ((ε.hom ≫ ε.inv).app (j ⁻¹ᵁ U)) e' = e'
      rw [Iso.hom_inv_id]
      rfl
    change Scheme.Modules.IsFreeGenerator
      (ε.inv.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackSection j e)) at h
    rwa [heq] at h
  let t : ULift.{u} (Fin r) → M.sections := fun i ↦ SheafOfModules.unitHomEquiv _
    (Scheme.Modules.homOfGlobalSection _ (Scheme.Modules.tensorSectionsUnit j L (s i.down)))
  have ht (i : ULift.{u} (Fin r)) :
      (t i).val (Opposite.op ⊤) = η.app ⊤ (s i.down) := by
    have h := Scheme.Modules.homOfGlobalSection_app_one M
      (Scheme.Modules.tensorSectionsUnit j L (s i.down)) ⊤
    change (t i).val (Opposite.op ⊤) = _ at h
    rw [Scheme.Modules.presheaf_map_id_apply] at h
    refine h.trans ?_
    change M.presheaf.map (homOfLE j.preimage_top.ge).op (η.app ⊤ (s i.down)) = _
    exact Scheme.Modules.presheaf_map_id_apply _ _
  have hcoeff (i : ULift.{u} (Fin r)) :
      he'.coeff (M.presheaf.map (homOfLE le_top).op ((t i).val (Opposite.op ⊤))) =
      j.app U (he.coeff (L.presheaf.map (homOfLE le_top).op (s i.down))) := by
    apply (he'.coeff_eq_iff _ _).mpr
    rw [ht]
    have hn := Scheme.Modules.Hom.app_presheaf_map η
      (homOfLE (le_top : U ≤ ⊤)) (s i.down)
    change η.app U (L.presheaf.map (homOfLE le_top).op (s i.down)) =
      M.presheaf.map (homOfLE le_top).op (η.app ⊤ (s i.down)) at hn
    rw [← hn]
    have hsmul := Scheme.Modules.Hom.app_smul η
      (he.coeff (L.presheaf.map (homOfLE le_top).op (s i.down))) e
    change η.app U (_ • e) = j.app U _ • e' at hsmul
    rw [he.coeff_smul] at hsmul
    exact hsmul.symm
  obtain ⟨i, v, hv, hfrac⟩ := generatingSections_local_fractions k
    (j ≫ (X ↘ Spec (.of k))) (ULift.{u} (Fin r)) M t hgen
    y (j ⁻¹ᵁ U) hxU e' he'
  let τ := (j.stalkMap y).hom
  let σ := (inv (j.stalkMap y)).hom
  let u : (X.presheaf.stalk x)ˣ := Units.map σ.toMonoidHom v
  let c : Fin r → X.presheaf.stalk x := fun a ↦ X.presheaf.germ U x hxU
    (he.coeff (L.presheaf.map (homOfLE le_top).op (s a)))
  let d : ULift.{u} (Fin r) → U₀.toScheme.presheaf.stalk y := fun a ↦
    U₀.toScheme.presheaf.germ (j ⁻¹ᵁ U) y hxU
      (he'.coeff (M.presheaf.map (homOfLE le_top).op ((t a).val (Opposite.op ⊤))))
  have hd (a : ULift.{u} (Fin r)) : d a = τ (c a.down) := by
    dsimp only [d, c, τ]
    rw [hcoeff]
    exact (j.germ_stalkMap_apply U y hxU _).symm
  have hστ (a : X.presheaf.stalk x) : σ (τ a) = a := by
    exact IsIso.hom_inv_id_apply (j.stalkMap y) a
  have hτσ (a : U₀.toScheme.presheaf.stalk y) : τ (σ a) = a := by
    exact IsIso.inv_hom_id_apply (j.stalkMap y) a
  have hu : (u : X.presheaf.stalk x) = c i.down := by
    change σ (v : U₀.toScheme.presheaf.stalk y) = _
    rw [show (v : U₀.toScheme.presheaf.stalk y) = d i from hv, hd, hστ]
  refine ⟨i.down, u, hu, ?_⟩
  let ρ : k →+* X.presheaf.stalk x :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (X ↘ Spec (.of k)).appTop.hom).comp
      (Scheme.ΓSpecIso (.of k)).inv.hom
  let ρ' : k →+* U₀.toScheme.presheaf.stalk y :=
    ((U₀.toScheme.presheaf.germ ⊤ y trivial).hom.comp
      (j ≫ (X ↘ Spec (.of k))).appTop.hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hρ : τ.comp ρ = ρ' := by
    ext a
    change j.stalkMap y (X.presheaf.germ ⊤ x trivial
      ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a))) =
        U₀.toScheme.presheaf.germ ⊤ y trivial
          ((j ≫ (X ↘ Spec (.of k))).appTop ((Scheme.ΓSpecIso (.of k)).inv a))
    rw [Scheme.Hom.comp_appTop]
    exact j.germ_stalkMap_apply ⊤ y trivial _
  have hvars (a : ULift.{u} (Fin r)) :
      τ ((↑u⁻¹ : X.presheaf.stalk x) * c a.down) =
        (↑v⁻¹ : U₀.toScheme.presheaf.stalk y) * d a := by
    rw [map_mul, ← hd]
    change τ (σ (↑v⁻¹ : U₀.toScheme.presheaf.stalk y)) * d a = _
    rw [hτσ]
  have hEval (p : MvPolynomial (ULift.{u} (Fin r)) k) :
      τ (MvPolynomial.eval₂Hom ρ (fun a ↦ (↑u⁻¹ : X.presheaf.stalk x) * c a)
        (MvPolynomial.rename ULift.down p)) =
      MvPolynomial.eval₂Hom ρ' (fun a ↦ (↑v⁻¹ : U₀.toScheme.presheaf.stalk y) * d a) p := by
    rw [MvPolynomial.eval₂Hom_rename]
    have hh : τ.comp (MvPolynomial.eval₂Hom ρ
        (fun a : ULift.{u} (Fin r) ↦ (↑u⁻¹ : X.presheaf.stalk x) * c a.down)) =
        MvPolynomial.eval₂Hom ρ'
          (fun a ↦ (↑v⁻¹ : U₀.toScheme.presheaf.stalk y) * d a) := by
      apply MvPolynomial.ringHom_ext
      · intro z
        simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C] using
          DFunLike.congr_fun hρ z
      · intro a
        simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X'] using hvars a
    exact DFunLike.congr_fun hh p
  intro a
  obtain ⟨p, q, hq, hpq⟩ := hfrac (τ a)
  refine ⟨MvPolynomial.rename ULift.down p, MvPolynomial.rename ULift.down q, ?_, ?_⟩
  · have h := hq.map σ
    rw [← hEval, hστ] at h
    exact h
  · apply (ConcreteCategory.bijective_of_isIso (j.stalkMap y)).1
    rw [map_mul, hEval, hEval]
    exact hpq

end AlgebraicGeometry
