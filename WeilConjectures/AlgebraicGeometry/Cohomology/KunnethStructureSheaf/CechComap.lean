/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural

/-!
# Pulling back Čech cochains of a direct image along a retraction

Let `i : X ⟶ Z` and `π : Z ⟶ X` be morphisms of schemes and let `W` be a family of opens of `Z`
indexed by `ι`, together with a map `s : ι → ι` such that `i (π z) ∈ W (s q)` for `z ∈ W q`.
Pulling back along `π` after reindexing by `s` defines maps of Čech cochains
`Č(W, i_* 𝒪_X) → Č(W, 𝒪_Z)` commuting with the differentials
(`AlgebraicGeometry.Scheme.cechCochainComap`). If `i ≫ π = 𝟙` and `s` fixes every index `q`
with `i ⁻¹ᵁ W q ≠ ⊥`, composing with `i^♯` gives the identity.

## Main definitions

- `AlgebraicGeometry.Scheme.cechCochainComap`

## Main statements

- `AlgebraicGeometry.Scheme.cechCochainComap_d`
- `AlgebraicGeometry.Scheme.cechComplex_map_f_cechCochainComap`
- `AlgebraicGeometry.Scheme.cechComplex_map_f_cechCochainComap_eq_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- A Čech `1`-cocycle vanishes on constant pairs of indices. -/
lemma cechCocycle_apply_const_eq_zero (c : CechCochain U P 1)
    (hc : ((cechComplex U).obj P).d 1 2 c = 0) (a : ι) : c (fun _ ↦ a) = 0 := by
  have h : ⨅ _ : Fin 3, U a ≤ ⨅ _ : Fin 2, U a := le_iInf fun _ ↦ iInf_le _ 0
  have h' : ⨅ _ : Fin 2, U a ≤ ⨅ _ : Fin 3, U a := le_iInf fun _ ↦ iInf_le _ 0
  have h0 := congrFun hc (fun _ ↦ a)
  rw [cechComplex_d_apply] at h0
  have hx (i : Fin 3) : P.map (homOfLE (iInf_le_iInf_comp U (fun _ ↦ a) i.succAbove)).op
      (c ((fun _ ↦ a) ∘ i.succAbove)) = P.map (homOfLE h).op (c fun _ ↦ a) := rfl
  simp only [hx] at h0
  rw [Fin.sum_univ_three] at h0
  have h1 : P.map (homOfLE h).op (c fun _ ↦ a) = 0 := by
    simpa using h0.trans (Pi.zero_apply _)
  have h2 := map_homOfLE_map_homOfLE_apply P h' h (c fun _ ↦ a)
  rw [h1, map_zero, map_homOfLE_self_apply] at h2
  exact h2.symm

/-- A Čech `1`-cocycle vanishes on pairs of equal indices. -/
lemma cechCocycle_apply_eq_zero_of_eq (c : CechCochain U P 1)
    (hc : ((cechComplex U).obj P).d 1 2 c = 0) (y : Fin 2 → ι) (hy : y 0 = y 1) : c y = 0 := by
  have hy' : y = fun _ ↦ y 0 := funext fun l ↦ by
    fin_cases l
    · rfl
    · exact hy.symm
  rw [hy']
  exact cechCocycle_apply_const_eq_zero U P c hc _

end TopCat.Presheaf

namespace AlgebraicGeometry.Scheme

/-- The structure sheaf of a scheme, as a presheaf of abelian groups. -/
noncomputable abbrev unitPresheaf (Z : Scheme.{u}) : Z.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf)).obj

/-- The direct image `i_* 𝒪_X`, as a presheaf of abelian groups. -/
noncomputable abbrev pushforwardUnitPresheaf {X Z : Scheme.{u}} (i : X ⟶ Z) :
    Z.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf Z.ringCatSheaf).obj
    ((SheafOfModules.pushforward i.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf))).obj

variable {X Y Z : Scheme.{u}} {ι : Type u} (W : ι → Z.Opens)

lemma mem_iInf_fin_iff {k : ℕ} (V : Fin (k + 1) → Z.Opens) (z : Z) :
    z ∈ ⨅ l, V l ↔ ∀ l, z ∈ V l := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- The map `i^♯ : 𝒪_Z → i_* 𝒪_X` on Čech cochains is `i^♯` on each component. -/
lemma cechComplex_map_unitToPushforwardObjUnit_f_apply (i : X ⟶ Z) (k : ℕ)
    (c : TopCat.Presheaf.CechCochain W Z.unitPresheaf k) (y : Fin (k + 1) → ι) :
    ((TopCat.Presheaf.cechComplex W).map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom).f k c y =
      i.app _ (c y) :=
  rfl

lemma unitPresheaf_map_apply {V V' : Z.Opensᵒᵖ} (f : V ⟶ V') (t : Z.unitPresheaf.obj V) :
    Z.unitPresheaf.map f t = Z.presheaf.map f t :=
  rfl

lemma pushforwardUnitPresheaf_map_apply (i : X ⟶ Z) {V V' : Z.Opens} (h : V' ≤ V)
    (t : (pushforwardUnitPresheaf i).obj (op V)) :
    (pushforwardUnitPresheaf i).map (homOfLE h).op t =
      X.presheaf.map (homOfLE (i.preimage_mono h)).op t :=
  rfl

/-- For `f = 𝟙`, `f.appLE` is a restriction map. -/
lemma Hom.appLE_eq_map_of_eq_id {f : X ⟶ X} (hf : f = 𝟙 X) (U V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V h = X.presheaf.map (homOfLE (h.trans (by rw [hf]; exact le_rfl))).op := by
  subst hf
  simp only [Hom.appLE, Hom.id_app]
  exact Category.id_comp _

/-- The map `Γ(V, i_* 𝒪_X) = Γ(X, i ⁻¹ᵁ V) → Γ(Z, V')` given by `π^♯`, for
`V' ≤ π ⁻¹ᵁ i ⁻¹ᵁ V`. -/
noncomputable def pushforwardUnitPresheafComap (i : X ⟶ Z) (π : Z ⟶ X) {V V' : Z.Opens}
    (h : V' ≤ π ⁻¹ᵁ i ⁻¹ᵁ V) :
    (pushforwardUnitPresheaf i).obj (op V) ⟶ Z.unitPresheaf.obj (op V') :=
  AddCommGrpCat.ofHom (π.appLE (i ⁻¹ᵁ V) V' h).hom.toAddMonoidHom

lemma map_pushforwardUnitPresheafComap (i : X ⟶ Z) (π : Z ⟶ X) {V₁ V₂ V' : Z.Opens}
    (h₁ : V₂ ≤ V₁) (h₂ : V' ≤ π ⁻¹ᵁ i ⁻¹ᵁ V₂) :
    (pushforwardUnitPresheaf i).map (homOfLE h₁).op ≫ pushforwardUnitPresheafComap i π h₂ =
      pushforwardUnitPresheafComap i π (h₂.trans (π.preimage_mono (i.preimage_mono h₁))) := by
  ext t
  exact ConcreteCategory.congr_hom (Hom.map_appLE π h₂ (homOfLE (i.preimage_mono h₁)).op) t

lemma pushforwardUnitPresheafComap_map (i : X ⟶ Z) (π : Z ⟶ X) {V V'₁ V'₂ : Z.Opens}
    (h₁ : V'₁ ≤ π ⁻¹ᵁ i ⁻¹ᵁ V) (h₂ : V'₂ ≤ V'₁) :
    pushforwardUnitPresheafComap i π h₁ ≫ Z.unitPresheaf.map (homOfLE h₂).op =
      pushforwardUnitPresheafComap i π (h₂.trans h₁) := by
  ext t
  exact ConcreteCategory.congr_hom (Hom.appLE_map π h₁ (homOfLE h₂).op) t

/-- If `i ≫ π = 𝟙`, then `i^♯ ∘ π^♯` is a restriction map. -/
lemma pushforwardUnitPresheafComap_unitToPushforwardObjUnit (i : X ⟶ Z) (π : Z ⟶ X)
    (hiπ : i ≫ π = 𝟙 X) {V V' : Z.Opens} (h : V' ≤ π ⁻¹ᵁ i ⁻¹ᵁ V) (h' : V' ≤ V) :
    pushforwardUnitPresheafComap i π h ≫ ((SheafOfModules.toSheaf Z.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom.app (op V') =
      (pushforwardUnitPresheaf i).map (homOfLE h').op := by
  have key : π.appLE (i ⁻¹ᵁ V) V' h ≫ i.app V' =
      X.presheaf.map (homOfLE (i.preimage_mono h')).op := by
    rw [Hom.app_eq_appLE, Hom.appLE_comp_appLE, Hom.appLE_eq_map_of_eq_id hiπ]
  ext t
  exact ConcreteCategory.congr_hom key t

lemma map_pushforwardUnitPresheafComap_apply (i : X ⟶ Z) (π : Z ⟶ X) {V₁ V₂ V' : Z.Opens}
    (h₁ : V₂ ≤ V₁) (h₂ : V' ≤ π ⁻¹ᵁ i ⁻¹ᵁ V₂) (t : (pushforwardUnitPresheaf i).obj (op V₁)) :
    pushforwardUnitPresheafComap i π h₂ ((pushforwardUnitPresheaf i).map (homOfLE h₁).op t) =
      pushforwardUnitPresheafComap i π (h₂.trans (π.preimage_mono (i.preimage_mono h₁))) t := by
  rw [← ConcreteCategory.comp_apply, map_pushforwardUnitPresheafComap]

lemma pushforwardUnitPresheafComap_map_apply (i : X ⟶ Z) (π : Z ⟶ X) {V V'₁ V'₂ : Z.Opens}
    (h₁ : V'₁ ≤ π ⁻¹ᵁ i ⁻¹ᵁ V) (h₂ : V'₂ ≤ V'₁) (t : (pushforwardUnitPresheaf i).obj (op V)) :
    Z.unitPresheaf.map (homOfLE h₂).op (pushforwardUnitPresheafComap i π h₁ t) =
      pushforwardUnitPresheafComap i π (h₂.trans h₁) t := by
  rw [← ConcreteCategory.comp_apply, pushforwardUnitPresheafComap_map]

lemma le_preimage_preimage_iInf (i : X ⟶ Z) (π : Z ⟶ X) (s : ι → ι)
    (hs : ∀ q, ∀ z ∈ W q, i (π z) ∈ W (s q)) {k : ℕ} (y : Fin (k + 1) → ι) :
    ⨅ l, W (y l) ≤ π ⁻¹ᵁ i ⁻¹ᵁ ⨅ l, W (s (y l)) := by
  intro z hz
  rw [Hom.mem_preimage, Hom.mem_preimage, mem_iInf_fin_iff]
  exact fun l ↦ hs _ z ((mem_iInf_fin_iff _ z).1 hz l)

variable (i : X ⟶ Z) (π : Z ⟶ X) (s : ι → ι) (hs : ∀ q, ∀ z ∈ W q, i (π z) ∈ W (s q))

/-- Pulling back Čech cochains of `i_* 𝒪_X` along `π`, after reindexing by `s`:
`(Φ e)(q₀, …, qₖ) = π^♯ e(s q₀, …, s qₖ)`. -/
noncomputable def cechCochainComap (k : ℕ) :
    TopCat.Presheaf.CechCochain W (pushforwardUnitPresheaf i) k →+
      TopCat.Presheaf.CechCochain W Z.unitPresheaf k where
  toFun e y := pushforwardUnitPresheafComap i π (le_preimage_preimage_iInf W i π s hs y)
    (e (s ∘ y))
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _ _ := funext fun _ ↦ map_add _ _ _

lemma cechCochainComap_apply (k : ℕ)
    (e : TopCat.Presheaf.CechCochain W (pushforwardUnitPresheaf i) k) (y : Fin (k + 1) → ι) :
    cechCochainComap W i π s hs k e y =
      pushforwardUnitPresheafComap i π (le_preimage_preimage_iInf W i π s hs y) (e (s ∘ y)) :=
  rfl

/-- `cechCochainComap` commutes with the Čech differentials. -/
lemma cechCochainComap_d (k : ℕ)
    (e : TopCat.Presheaf.CechCochain W (pushforwardUnitPresheaf i) k) :
    cechCochainComap W i π s hs (k + 1)
        (((TopCat.Presheaf.cechComplex W).obj (pushforwardUnitPresheaf i)).d k (k + 1) e) =
      ((TopCat.Presheaf.cechComplex W).obj Z.unitPresheaf).d k (k + 1)
        (cechCochainComap W i π s hs k e) := by
  funext y
  dsimp only [cechCochainComap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [TopCat.Presheaf.cechComplex_d_apply,
    TopCat.Presheaf.cechComplex_d_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_zsmul]
  congr 1
  exact (map_pushforwardUnitPresheafComap_apply i π _ _ _).trans
    (pushforwardUnitPresheafComap_map_apply i π _ _ _).symm

/-- If `i ≫ π = 𝟙` and `s` fixes every index `q` with `i ⁻¹ᵁ W q ≠ ⊥`, then `i^♯` is a left
inverse of `cechCochainComap`. -/
lemma cechComplex_map_f_cechCochainComap (hiπ : i ≫ π = 𝟙 X)
    (hfix : ∀ q, s q = q ∨ i ⁻¹ᵁ W q = ⊥) (k : ℕ)
    (e : TopCat.Presheaf.CechCochain W (pushforwardUnitPresheaf i) k) :
    ((TopCat.Presheaf.cechComplex W).map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom).f k
        (cechCochainComap W i π s hs k e) = e := by
  funext y
  rw [TopCat.Presheaf.cechComplex_map_f_apply, cechCochainComap_apply]
  by_cases h : ∀ l, s (y l) = y l
  · have hle : ⨅ l, W (y l) ≤ ⨅ l, W (s (y l)) :=
      le_iInf fun l ↦ (iInf_le _ l).trans (congrArg W (h l)).ge
    rw [← ConcreteCategory.comp_apply,
      pushforwardUnitPresheafComap_unitToPushforwardObjUnit i π hiπ _ hle]
    exact (TopCat.Presheaf.map_homOfLE_apply_congr W _ e (funext h : s ∘ y = y) hle le_rfl).trans
      (TopCat.Presheaf.map_homOfLE_self_apply _ _ _)
  · obtain ⟨l, hl⟩ := not_forall.1 h
    have hbot : i ⁻¹ᵁ ⨅ l, W (y l) = ⊥ :=
      eq_bot_iff.2 ((i.preimage_mono (iInf_le _ l)).trans ((hfix (y l)).resolve_left hl).le)
    have : Subsingleton ((pushforwardUnitPresheaf i).obj (op (⨅ l, W (y l)))) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

/-- If `s` maps every index `q` with `j ⁻¹ᵁ W q ≠ ⊥` to a fixed index `q₀`, then `j^♯` kills the
image of a `1`-cocycle under `cechCochainComap`. -/
lemma cechComplex_map_f_cechCochainComap_eq_zero (j : Y ⟶ Z) (q₀ : ι)
    (hs₀ : ∀ q, s q = q₀ ∨ j ⁻¹ᵁ W q = ⊥)
    (e : TopCat.Presheaf.CechCochain W (pushforwardUnitPresheaf i) 1)
    (he : ((TopCat.Presheaf.cechComplex W).obj (pushforwardUnitPresheaf i)).d 1 2 e = 0) :
    ((TopCat.Presheaf.cechComplex W).map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).hom).f 1
        (cechCochainComap W i π s hs 1 e) = 0 := by
  funext y
  rw [TopCat.Presheaf.cechComplex_map_f_apply, cechCochainComap_apply]
  by_cases h : ∀ l, s (y l) = q₀
  · rw [TopCat.Presheaf.cechCocycle_apply_eq_zero_of_eq W _ e he _ ((h 0).trans (h 1).symm),
      map_zero, map_zero]
    rfl
  · obtain ⟨l, hl⟩ := not_forall.1 h
    have hbot : j ⁻¹ᵁ ⨅ l, W (y l) = ⊥ :=
      eq_bot_iff.2 ((j.preimage_mono (iInf_le _ l)).trans ((hs₀ (y l)).resolve_left hl).le)
    have : Subsingleton ((pushforwardUnitPresheaf j).obj (op (⨅ l, W (y l)))) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme
