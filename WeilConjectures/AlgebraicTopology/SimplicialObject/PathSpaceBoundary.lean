/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.PrismValue
public import WeilConjectures.AlgebraicTopology.SimplicialObject.MatchingCone

/-!
# Filling boundaries of the path space

Let `a b : U ⟶ V` be maps of simplicial objects in a category with finite limits and let `p` be
a boundary cone of degree `N` of `pathSpace a b`. We reduce the problem of filling `p` to
filling boundaries in `U` and `V`: first an `N`-simplex `u` of `U` with boundary the projection
of `p`, then the interior `N`-simplices `τ s` of the prism `Δ[N] × Δ[1]` (with boundaries
`tauCone p s`), and finally the `N + 1` prism simplices (with boundaries `prismCone`). The
result is `exists_ofSimplex_eq_precomp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SimplexCategory SimplicialObject

namespace CategoryTheory

variable {C : Type*} [Category* C] {U V : SimplicialObject C} {a b : U ⟶ V} [HasFiniteLimits C]
  {N : ℕ} {T : C} (p : BoundaryCone (pathSpace a b) N T)

namespace PathSpaceBoundary

/-- The value of the boundary `p` on the simplex `(f, g)` of `∂Δ[N] × Δ[1]`. -/
noncomputable def bval {Δ : SimplexCategory} (f : Δ ⟶ ⦋N⦌) (hf : ¬ Epi f) (g : Δ ⟶ ⦋1⦌) :
    T ⟶ V.obj (op Δ) :=
  pathValue a b (r := Δ.len) (p.descApp f hf) (𝟙 Δ) g

lemma bval_congr {Δ : SimplexCategory} {f f' : Δ ⟶ ⦋N⦌} (hf : ¬ Epi f) (hf' : ¬ Epi f')
    {g g' : Δ ⟶ ⦋1⦌} (h : f = f') (hg : g = g') : bval p f hf g = bval p f' hf' g' := by
  subst h hg
  rfl

lemma bval_comp {Δ Δ' : SimplexCategory} (f : Δ ⟶ ⦋N⦌) (hf : ¬ Epi f) (g : Δ ⟶ ⦋1⦌)
    (θ : Δ' ⟶ Δ) (hf' : ¬ Epi (θ ≫ f)) :
    bval p f hf g ≫ V.map θ.op = bval p (θ ≫ f) hf' (θ ≫ g) := by
  obtain ⟨m, rfl⟩ : ∃ m, Δ' = ⦋m⦌ := ⟨Δ'.len, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, Δ = ⦋n⦌ := ⟨Δ.len, rfl⟩
  rw [bval, bval, pathValue_comp, p.descApp_comp f hf θ hf']
  exact ((pathValue_map (p.descApp f hf) θ (𝟙 _) (θ ≫ g)).trans (by simp)).symm

lemma bval_precomp {T' : C} (t : T' ⟶ T) {Δ : SimplexCategory} (f : Δ ⟶ ⦋N⦌) (hf : ¬ Epi f)
    (g : Δ ⟶ ⦋1⦌) : bval (p.precomp t) f hf g = t ≫ bval p f hf g := by
  rw [bval, bval, ← pathValue_precomp]
  congr 1
  simp [BoundaryCone.descApp]

lemma bval_eq_pathValue {n : ℕ} (hn : n < N) (β : ⦋n⦌ ⟶ ⦋N⦌) {Δ : SimplexCategory}
    (α : Δ ⟶ ⦋n⦌) (h : ¬ Epi (α ≫ β)) (g : Δ ⟶ ⦋1⦌) :
    bval p (α ≫ β) h g = pathValue a b (p.π ⦋n⦌ (by simpa using hn) β) α g := by
  obtain ⟨m, rfl⟩ : ∃ m, Δ = ⦋m⦌ := ⟨Δ.len, rfl⟩
  have hβ : ¬ Epi β := not_epi_of_len_lt β (by simpa using hn)
  rw [bval, p.descApp_comp β hβ α h, p.descApp_eq_π β hβ (by simpa using hn)]
  exact (pathValue_map _ α (𝟙 _) g).trans (by simp)

/-- The boundary of the interior `N`-simplex of the prism switching at `s`. -/
noncomputable def tauCone (s : Fin (N + 2)) : BoundaryCone V N T where
  π Δ hΔ θ := bval p θ (not_epi_of_len_lt θ hΔ) (θ ≫ sw s)
  w Δ Δ' h h' α θ := by
    rw [bval_comp (hf' := not_epi_of_len_lt _ h')]
    exact bval_congr _ _ _ rfl (Category.assoc _ _ _).symm

lemma tauCone_descApp (s : Fin (N + 2)) {Δ : SimplexCategory} (μ : Δ ⟶ ⦋N⦌) (hμ : ¬ Epi μ) :
    (tauCone p s).descApp μ hμ = bval p μ hμ (μ ≫ sw s) := by
  rw [BoundaryCone.descApp]
  dsimp only [tauCone]
  rw [bval_comp (hf' := by rw [image.fac]; exact hμ)]
  exact bval_congr _ _ _ (image.fac μ) (by rw [image.fac_assoc])

lemma tauCone_precomp {T' : C} (t : T' ⟶ T) (s : Fin (N + 2)) :
    (tauCone p s).precomp t = tauCone (p.precomp t) s :=
  BoundaryCone.ext' fun Δ hΔ θ ↦ by
    simp only [BoundaryCone.precomp_π, tauCone, bval_precomp]

variable {p} {u : T ⟶ U _⦋N⦌} (hu : BoundaryCone.ofSimplex u = p.postcomp (pathProj a b))

include hu in
lemma descApp_pathU {Δ : SimplexCategory} (f : Δ ⟶ ⦋N⦌) (hf : ¬ Epi f) :
    p.descApp f hf ≫ pathU a b Δ.len = u ≫ U.map f.op := by
  have := congrArg (fun c ↦ BoundaryCone.descApp c f hf) hu
  simp only [BoundaryCone.descApp_ofSimplex, BoundaryCone.descApp_postcomp] at this
  exact this.symm

variable (u) in
/-- The interior `N`-simplices of the prism, with the two ends given by `u`. -/
noncomputable def tau' (τ : Fin (N + 2) → (T ⟶ V _⦋N⦌)) (s : Fin (N + 2)) : T ⟶ V _⦋N⦌ :=
  if s = 0 then u ≫ b.app _ else if s = Fin.last (N + 1) then u ≫ a.app _ else τ s

variable {τ : Fin (N + 2) → (T ⟶ V _⦋N⦌)}
  (hτ : ∀ s, BoundaryCone.ofSimplex (τ s) = tauCone p s)

include hu hτ in
lemma tau'_map (s : Fin (N + 2)) {Δ : SimplexCategory} (μ : Δ ⟶ ⦋N⦌) (hμ : ¬ Epi μ) :
    tau' u τ s ≫ V.map μ.op = bval p μ hμ (μ ≫ sw s) := by
  obtain ⟨m, rfl⟩ : ∃ m, Δ = ⦋m⦌ := ⟨Δ.len, rfl⟩
  unfold tau'
  split_ifs with h₀ h₁
  · subst h₀
    rw [bval, pathValue_of_one _ _ (fun x ↦ by
      simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, sw_zero_val])]
    erw [← Category.assoc, descApp_pathU hu]
    simp
  · subst h₁
    rw [bval, pathValue_of_zero _ _ (fun x ↦ by
      simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, sw_last_val])]
    erw [← Category.assoc, descApp_pathU hu]
    simp
  · rw [← BoundaryCone.descApp_ofSimplex, hτ, tauCone_descApp]

variable (p u τ) in
/-- The faces of the prism simplices: `tau'` on the interior faces and the boundary values on
the other ones. -/
noncomputable def hval (f : ⦋N⦌ ⟶ ⦋N⦌) (g : ⦋N⦌ ⟶ ⦋1⦌) : T ⟶ V _⦋N⦌ := by
  classical
  exact if hf : Epi f then tau' u τ (switch g) else bval p f hf g

lemma hval_id (g : ⦋N⦌ ⟶ ⦋1⦌) : hval p u τ (𝟙 _) g = tau' u τ (switch g) := by
  rw [hval, dif_pos inferInstance]

include hu hτ in
lemma hval_map (f : ⦋N⦌ ⟶ ⦋N⦌) (g : ⦋N⦌ ⟶ ⦋1⦌) {Δ : SimplexCategory} (μ : Δ ⟶ ⦋N⦌)
    (h : ¬ Epi (μ ≫ f)) : hval p u τ f g ≫ V.map μ.op = bval p (μ ≫ f) h (μ ≫ g) := by
  by_cases hf : Epi f
  · obtain rfl := eq_id_of_epi f
    have hμ : ¬ Epi μ := by simpa using h
    rw [hval_id, tau'_map hu hτ _ μ hμ, sw_switch]
    exact bval_congr _ _ _ (Category.comp_id _).symm rfl
  · rw [hval, dif_neg hf, bval_comp]

variable (p u τ) in
/-- The faces of the `k`-th prism simplex. -/
noncomputable def hFaces (k : Fin (N + 1)) (j : Fin (N + 2)) : T ⟶ V _⦋N⦌ :=
  hval p u τ (δ j ≫ σ k) (δ j ≫ side k)

include hu hτ in
lemma isBoundaryFamily_hFaces (k : Fin (N + 1)) : V.IsBoundaryFamily (hFaces p u τ k) := by
  rcases N with _ | n
  · exact V.isBoundaryFamily_zero _
  · refine V.isBoundaryFamily_succ _ fun i j hij ↦ ?_
    simp only [hFaces, SimplicialObject.δ]
    rw [hval_map hu hτ _ _ _ (not_epi_of_len_lt _ (by simp)),
      hval_map hu hτ _ _ _ (not_epi_of_len_lt _ (by simp))]
    exact bval_congr _ _ _
      (by rw [← Category.assoc, ← Category.assoc, SimplexCategory.δ_comp_δ hij])
      (by rw [← Category.assoc, ← Category.assoc, SimplexCategory.δ_comp_δ hij])

/-- The boundary of the `k`-th prism simplex. -/
noncomputable def prismCone (k : Fin (N + 1)) : BoundaryCone V (N + 1) T :=
  BoundaryCone.ofFaces (hFaces p u τ k) (isBoundaryFamily_hFaces hu hτ k)

include hτ in
/-- A boundary of the path space can be filled once the boundaries of `u`, the interior
simplices and the prism simplices are filled. -/
theorem exists_ofSimplex_eq_precomp {T' : C} (t : T' ⟶ T)
    (h : Fin (N + 1) → (T' ⟶ V _⦋N + 1⦌))
    (hh : ∀ k, BoundaryCone.ofSimplex (h k) = (prismCone hu hτ k).precomp t) :
    ∃ z : T' ⟶ (pathSpace a b) _⦋N⦌, BoundaryCone.ofSimplex z = p.precomp t := by
  have hface : ∀ k J, h k ≫ V.δ J = t ≫ hFaces p u τ k J := fun k J ↦ by
    have := congrArg (fun c ↦ BoundaryCone.π c ⦋N⦌ (by simp) (δ J)) (hh k)
    simpa [prismCone] using this
  have hmap : ∀ (k : Fin (N + 1)) {Δ : SimplexCategory} (φ : Δ ⟶ ⦋N + 1⦌)
      (hφ : ¬ Epi (φ ≫ σ k)), h k ≫ V.map φ.op = t ≫ bval p (φ ≫ σ k) hφ (φ ≫ side k) := by
    intro k Δ φ hφ
    have hφ' : ¬ Function.Surjective φ.toOrderHom := fun hs ↦
      hφ (@epi_comp _ _ _ _ _ _ (SimplexCategory.epi_iff_surjective.2 hs) _ inferInstance)
    simp only [Function.Surjective, not_forall, not_exists] at hφ'
    obtain ⟨J, hJ⟩ := hφ'
    obtain ⟨φ', rfl⟩ := eq_comp_δ_of_not_surjective' φ J hJ
    rw [op_comp, V.map_comp, ← Category.assoc]
    erw [hface k J]
    rw [Category.assoc, hFaces, hval_map hu hτ _ _ φ' (by simpa using hφ)]
    exact bval_congr _ _ _ (by simp) (by simp)
  have hpath : V.IsPathFamily h := fun j ↦ by
    have e₁ : δ j.succ.castSucc ≫ σ j.succ = 𝟙 _ := SimplexCategory.δ_comp_σ_self
    have e₂ : δ j.succ.castSucc ≫ σ j.castSucc = 𝟙 _ := by
      rw [← Fin.succ_castSucc]; exact SimplexCategory.δ_comp_σ_succ
    have e₃ : δ j.succ.castSucc ≫ side j.succ = sw j.succ.castSucc := δ_castSucc_comp_side _
    have e₄ : δ j.succ.castSucc ≫ side j.castSucc = sw j.succ.castSucc := by
      rw [← Fin.succ_castSucc]; exact δ_succ_comp_side _
    rw [hface, hface, hFaces, hFaces, e₁, e₂, e₃, e₄]
  have h₀ : h 0 ≫ V.δ 0 = (t ≫ u) ≫ b.app _ := by
    have e₁ : δ (0 : Fin (N + 2)) ≫ σ (0 : Fin (N + 1)) = 𝟙 _ := by
      simpa using SimplexCategory.δ_comp_σ_self (i := (0 : Fin (N + 1)))
    have e₂ : δ (0 : Fin (N + 2)) ≫ side (0 : Fin (N + 1)) = sw 0 := by
      simpa using δ_castSucc_comp_side (0 : Fin (N + 1))
    rw [hface, hFaces, e₁, e₂, hval_id, switch_sw, tau', if_pos rfl, Category.assoc]
  have h₁ : h (Fin.last N) ≫ V.δ (Fin.last (N + 1)) = (t ≫ u) ≫ a.app _ := by
    have e₁ : δ (Fin.last (N + 1)) ≫ σ (Fin.last N) = 𝟙 _ := by
      rw [← Fin.succ_last]; exact SimplexCategory.δ_comp_σ_succ
    have e₂ : δ (Fin.last (N + 1)) ≫ side (Fin.last N) = sw (Fin.last (N + 1)) := by
      rw [← Fin.succ_last]; exact δ_succ_comp_side _
    rw [hface, hFaces, e₁, e₂, hval_id, switch_sw, tau', if_neg (Fin.last_pos.ne'),
      if_pos rfl, Category.assoc]
  refine ⟨pathLift a b (t ≫ u) h hpath h₀ h₁, ?_⟩
  rcases N with _ | n
  · exact BoundaryCone.eq_of_zero _ _
  refine BoundaryCone.ext_of_faces fun i ↦ ?_
  change pathLift a b (t ≫ u) h hpath h₀ h₁ ≫ (pathSpace a b).map (δ i).op =
    t ≫ p.π ⦋n⦌ _ (δ i)
  have hi : ¬ Epi (δ i) := not_epi_of_len_lt _ (by simp)
  refine pathObj_hom_ext a b ?_ fun l ↦ ?_
  · have := congrArg (fun c ↦ BoundaryCone.π c ⦋n⦌ (by simp) (δ i)) hu
    simp only [BoundaryCone.ofSimplex_π, BoundaryCone.postcomp_π, pathProj_app] at this
    rw [Category.assoc, Category.assoc]
    erw [pathMapObj_pathU, pathLift_pathU_assoc]
    rw [Category.assoc, this]
    rfl
  · rw [Category.assoc, Category.assoc, pathSpace_map_pathH, pathLift_pathH_assoc,
      hmap _ _ (by rw [prism_comp_σ]; exact not_epi_comp_of_not_epi _ _ hi),
      ← pathValue_σ_side, ← bval_eq_pathValue p (by omega) (δ i) (σ l)
        (not_epi_comp_of_not_epi _ _ hi)]
    exact congrArg _ (bval_congr _ _ _ (prism_comp_σ _ _) (prism_comp_side _ _))

end PathSpaceBoundary

end CategoryTheory
