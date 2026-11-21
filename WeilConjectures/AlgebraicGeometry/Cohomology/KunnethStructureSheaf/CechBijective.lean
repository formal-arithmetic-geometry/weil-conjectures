/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomologyMapOneProd
public import WeilConjectures.AlgebraicGeometry.Cohomology.KunnethStructureSheaf.IdealCocycle

/-!
# Čech `H¹` of `𝒪` on a product restricted to two slices

Let `X`, `Y` be schemes over a field `K` with `K`-points `x`, `y`, and let `i : X ⟶ X ×_K Y`,
`j : Y ⟶ X ×_K Y` be the slices through `y` and `x`. For finite affine covers of `X` and `Y` in
which exactly one member contains `x`, respectively `y`, restriction to the two slices is a
bijection on the first Čech cohomology of `𝒪` for the product cover.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_homologyMap_cechComplex_slices`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

open IdealSheafData.Kunneth

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))]

/-- Let `x`, `y` be `K`-points of `X`, `Y` whose ideal sheaves have no nonzero global sections,
and let `i : X ⟶ X ×_K Y`, `j : Y ⟶ X ×_K Y` be sections of the projections which are the base
changes of `y` and `x`. Let `Ux`, `Vy` be finite affine covers of `X`, `Y` with affine pairwise
intersections, in which exactly one member contains `x`, respectively `y`, and whose product
cover `W` has affine finite intersections. Then `(i^♯, j^♯)` is a bijection
`Ȟ¹(W, 𝒪) → Ȟ¹(W, i_* 𝒪_X) × Ȟ¹(W, j_* 𝒪_Y)`. -/
lemma bijective_homologyMap_cechComplex_slices {α β : Type u} [Finite α] [Finite β]
    (Ux : α → X.Opens) (Vy : β → Y.Opens) (hUx : ∀ a, IsAffineOpen (Ux a))
    (hVy : ∀ b, IsAffineOpen (Vy b)) (hUx₂ : ∀ a a', IsAffineOpen (Ux a ⊓ Ux a'))
    (hVy₂ : ∀ b b', IsAffineOpen (Vy b ⊓ Vy b')) (hUcov : iSup Ux = ⊤) (hVcov : iSup Vy = ⊤)
    (hW : ∀ (k : ℕ) (q : Fin (k + 1) → α × β),
      IsAffineOpen (⨅ l, prodOpen K X Y (Ux (q l).1) (Vy (q l).2)))
    (x : Spec (.of K) ⟶ X) [IsClosedImmersion x] (y : Spec (.of K) ⟶ Y) [IsClosedImmersion y]
    (hI : ∀ s ∈ x.ker.idealOfOpens ⊤, s = 0) (hI' : ∀ s ∈ y.ker.idealOfOpens ⊤, s = 0)
    (a₀ : α) (b₀ : β) (ha₀ : ∀ a, x default ∈ Ux a ↔ a = a₀)
    (hb₀ : ∀ b, y default ∈ Vy b ↔ b = b₀)
    (i : X ⟶ prod K X Y) (j : Y ⟶ prod K X Y)
    (hi : IsPullback i (X ↘ Spec (.of K)) (prodSnd K X Y) y)
    (hj : IsPullback j (Y ↘ Spec (.of K)) (prodFst K X Y) x)
    (hi₁ : i ≫ prodFst K X Y = 𝟙 X) (hj₂ : j ≫ prodSnd K X Y = 𝟙 Y) :
    Function.Bijective fun c : ((TopCat.Presheaf.cechComplex
        (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).obj
          (prod K X Y).unitPresheaf).homology 1 ↦
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex
          (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).map
          ((SheafOfModules.toSheaf _).map
            (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom) 1 c,
        HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex
          (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).map
          ((SheafOfModules.toSheaf _).map
            (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).hom) 1 c) := by
  let W : α × β → (prod K X Y).Opens := fun p ↦ prodOpen K X Y (Ux p.1) (Vy p.2)
  -- the points `i w` and `j w`
  have hi₁' (w : X) : prodFst K X Y (i w) = w := by
    rw [← Hom.comp_apply, hi₁]
    rfl
  have hi₂' (w : X) : prodSnd K X Y (i w) = y default := by
    rw [← Hom.comp_apply, hi.w, Hom.comp_apply, Subsingleton.elim ((X ↘ Spec (.of K)) w) default]
  have hj₂' (w : Y) : prodSnd K X Y (j w) = w := by
    rw [← Hom.comp_apply, hj₂]
    rfl
  have hj₁' (w : Y) : prodFst K X Y (j w) = x default := by
    rw [← Hom.comp_apply, hj.w, Hom.comp_apply, Subsingleton.elim ((Y ↘ Spec (.of K)) w) default]
  have hibot (q : α × β) (hq : q.2 ≠ b₀) : i ⁻¹ᵁ W q = ⊥ :=
    eq_bot_iff.2 fun w hw ↦ hq ((hb₀ _).1 (hi₂' w ▸ hw.2))
  have hjbot (q : α × β) (hq : q.1 ≠ a₀) : j ⁻¹ᵁ W q = ⊥ :=
    eq_bot_iff.2 fun w hw ↦ hq ((ha₀ _).1 (hj₁' w ▸ hw.1))
  -- the two retractions of Čech cochains
  let s₁ : α × β → α × β := fun q ↦ (q.1, b₀)
  let s₂ : α × β → α × β := fun q ↦ (a₀, q.2)
  have hs₁ (q : α × β) (z) (hz : z ∈ W q) : i (prodFst K X Y z) ∈ W (s₁ q) :=
    ⟨by simpa [hi₁'] using hz.1, by simpa [hi₂'] using (hb₀ b₀).2 rfl⟩
  have hs₂ (q : α × β) (z) (hz : z ∈ W q) : j (prodSnd K X Y z) ∈ W (s₂ q) :=
    ⟨by simpa [hj₁'] using (ha₀ a₀).2 rfl, by simpa [hj₂'] using hz.2⟩
  have hfix₁ (q : α × β) : s₁ q = q ∨ i ⁻¹ᵁ W q = ⊥ := by
    by_cases hq : q.2 = b₀
    · exact .inl (Prod.ext rfl hq.symm)
    · exact .inr (hibot q hq)
  have hfix₂ (q : α × β) : s₂ q = q ∨ j ⁻¹ᵁ W q = ⊥ := by
    by_cases hq : q.1 = a₀
    · exact .inl (Prod.ext hq.symm rfl)
    · exact .inr (hjbot q hq)
  have hs₁₀ (q : α × β) : s₁ q = (a₀, b₀) ∨ j ⁻¹ᵁ W q = ⊥ := by
    by_cases hq : q.1 = a₀
    · exact .inl (Prod.ext hq rfl)
    · exact .inr (hjbot q hq)
  have hs₂₀ (q : α × β) : s₂ q = (a₀, b₀) ∨ i ⁻¹ᵁ W q = ⊥ := by
    by_cases hq : q.2 = b₀
    · exact .inl (Prod.ext rfl hq)
    · exact .inr (hibot q hq)
  -- the complexes and the maps between them
  let C := (TopCat.Presheaf.cechComplex W).obj (prod K X Y).unitPresheaf
  let D₁ := (TopCat.Presheaf.cechComplex W).obj (pushforwardUnitPresheaf i)
  let D₂ := (TopCat.Presheaf.cechComplex W).obj (pushforwardUnitPresheaf j)
  let f₁ := (TopCat.Presheaf.cechComplex W).map ((SheafOfModules.toSheaf _).map
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom
  let f₂ := (TopCat.Presheaf.cechComplex W).map ((SheafOfModules.toSheaf _).map
    (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).hom
  let Φ₁ (k : ℕ) : D₁.X k →+ C.X k := cechCochainComap W i (prodFst K X Y) s₁ hs₁ k
  let Φ₂ (k : ℕ) : D₂.X k →+ C.X k := cechCochainComap W j (prodSnd K X Y) s₂ hs₂ k
  have hΦ₁d₀ (g : D₁.X 0) : Φ₁ 1 (D₁.d 0 1 g) = C.d 0 1 (Φ₁ 0 g) :=
    cechCochainComap_d W i _ s₁ hs₁ 0 g
  have hΦ₁d₁ (e : D₁.X 1) : Φ₁ 2 (D₁.d 1 2 e) = C.d 1 2 (Φ₁ 1 e) :=
    cechCochainComap_d W i _ s₁ hs₁ 1 e
  have hΦ₂d₀ (g : D₂.X 0) : Φ₂ 1 (D₂.d 0 1 g) = C.d 0 1 (Φ₂ 0 g) :=
    cechCochainComap_d W j _ s₂ hs₂ 0 g
  have hΦ₂d₁ (e : D₂.X 1) : Φ₂ 2 (D₂.d 1 2 e) = C.d 1 2 (Φ₂ 1 e) :=
    cechCochainComap_d W j _ s₂ hs₂ 1 e
  have hf₁Φ₁ (k : ℕ) (e : D₁.X k) : f₁.f k (Φ₁ k e) = e :=
    cechComplex_map_f_cechCochainComap W i _ s₁ hs₁ hi₁ hfix₁ k e
  have hf₂Φ₂ (k : ℕ) (e : D₂.X k) : f₂.f k (Φ₂ k e) = e :=
    cechComplex_map_f_cechCochainComap W j _ s₂ hs₂ hj₂ hfix₂ k e
  have hf₂Φ₁ (e : D₁.X 1) (he : D₁.d 1 2 e = 0) : f₂.f 1 (Φ₁ 1 e) = 0 :=
    cechComplex_map_f_cechCochainComap_eq_zero W i _ s₁ hs₁ j (a₀, b₀) hs₁₀ e he
  have hf₁Φ₂ (e : D₂.X 1) (he : D₂.d 1 2 e = 0) : f₁.f 1 (Φ₂ 1 e) = 0 :=
    cechComplex_map_f_cechCochainComap_eq_zero W j _ s₂ hs₂ i (a₀, b₀) hs₂₀ e he
  have hf₁d₀ (c : C.X 0) : f₁.f 1 (C.d 0 1 c) = D₁.d 0 1 (f₁.f 0 c) :=
    (ConcreteCategory.congr_hom (f₁.comm 0 1) c).symm
  have hf₁d₁ (c : C.X 1) : f₁.f 2 (C.d 1 2 c) = D₁.d 1 2 (f₁.f 1 c) :=
    (ConcreteCategory.congr_hom (f₁.comm 1 2) c).symm
  have hf₂d₀ (c : C.X 0) : f₂.f 1 (C.d 0 1 c) = D₂.d 0 1 (f₂.f 0 c) :=
    (ConcreteCategory.congr_hom (f₂.comm 0 1) c).symm
  have hf₂d₁ (c : C.X 1) : f₂.f 2 (C.d 1 2 c) = D₂.d 1 2 (f₂.f 1 c) :=
    (ConcreteCategory.congr_hom (f₂.comm 1 2) c).symm
  have hdd (c : C.X 0) : C.d 1 2 (C.d 0 1 c) = 0 :=
    ConcreteCategory.congr_hom (C.d_comp_d 0 1 2) c
  refine HomologicalComplex.bijective_homologyMap_one_prod f₁ f₂ ?_ ?_
  · rintro c hc ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
    have hc₁ : D₁.d 1 2 (f₁.f 1 c) = 0 := by
      rw [← hf₁d₁, hc, map_zero]
    have hc₂ : D₂.d 1 2 (f₂.f 1 c) = 0 := by
      rw [← hf₂d₁, hc, map_zero]
    have hd : C.d 1 2 (c - C.d 0 1 (Φ₁ 0 g₁) - C.d 0 1 (Φ₂ 0 g₂)) = 0 := by
      rw [map_sub, map_sub, hc, hdd, hdd]
      simp
    have h₁ : f₁.f 1 (c - C.d 0 1 (Φ₁ 0 g₁) - C.d 0 1 (Φ₂ 0 g₂)) = 0 := by
      rw [map_sub, map_sub, hf₁d₀, hf₁Φ₁, hg₁, ← hΦ₂d₀, hg₂, hf₁Φ₂ _ hc₂, sub_self, sub_zero]
    have h₂ : f₂.f 1 (c - C.d 0 1 (Φ₁ 0 g₁) - C.d 0 1 (Φ₂ 0 g₂)) = 0 := by
      rw [map_sub, map_sub, hf₂d₀ (Φ₂ 0 g₂), hf₂Φ₂, hg₂, ← hΦ₁d₀, hg₁, hf₂Φ₁ _ hc₁, sub_zero,
        sub_self]
    obtain ⟨t, ht⟩ := exists_cechComplex_d_eq_of_unitToPushforwardObjUnit_eq_zero Ux Vy hUx hVy
      hUx₂ hVy₂ hUcov hVcov hW x y hI hI' i j hi hj _ hd h₁ h₂
    refine ⟨t + Φ₁ 0 g₁ + Φ₂ 0 g₂, ?_⟩
    rw [map_add, map_add, ht]
    abel
  · intro e₁ he₁ e₂ he₂
    refine ⟨Φ₁ 1 e₁ + Φ₂ 1 e₂, ?_, ?_, ?_⟩
    · rw [map_add, ← hΦ₁d₁, ← hΦ₂d₁, he₁, he₂, map_zero, map_zero, add_zero]
    · rw [map_add, hf₁Φ₁, hf₁Φ₂ _ he₂, add_zero]
    · rw [map_add, hf₂Φ₁ _ he₁, hf₂Φ₂, zero_add]

end AlgebraicGeometry.Scheme
