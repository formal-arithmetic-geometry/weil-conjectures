/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.CategoryTheory.SimplicialBoundaryFaces

/-!
# Local cones in split étale hypercovers

Let `U` be a split étale hypercover of `X` and `T` an étale `X`-scheme. Given finitely many
simplices `T ⟶ U_k` (closed under faces), we construct, after passing to a surjective étale
`T' ⟶ T`, a vertex `v : T' ⟶ U_0` and a cone on these simplices with vertex `v`: for every
simplex `τ` of degree `k` a simplex `h τ : T' ⟶ U_{k+1}` with `d₀ (h τ) = τ`,
`d_{i+1} (h τ) = h (d_i τ)` and, in degree `0`, `d₁ (h τ) = v`. This uses that the matching
maps `U_n ⟶ M_n(U)` are surjective étale.

## Main results

- `AlgebraicGeometry.SplitEtaleHypercover.exists_cover_lift`: lifting a compatible family of
  boundary simplices to a simplex after a surjective étale cover.
- `AlgebraicGeometry.SplitEtaleHypercover.exists_cover_forall`: finitely many local
  conditions can be achieved simultaneously.
- `AlgebraicGeometry.SplitEtaleHypercover.exists_cone`: the local cone construction.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X : Scheme.{w}}

/-- In the small étale site, the base change of a morphism which is surjective on underlying
schemes is surjective on underlying schemes. -/
lemma surjective_pullback_fst_left {Y Z W : X.Etale} (f : Y ⟶ W) (g : Z ⟶ W)
    [Surjective g.left] : Surjective (pullback.fst f g).left := by
  have h : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map (Scheme.Etale.forget X ⋙ Over.forget X)
  exact MorphismProperty.of_isPullback (P := @Surjective) h ‹_›

lemma surjective_id_left (T : X.Etale) : Surjective (𝟙 T : T ⟶ T).left :=
  inferInstanceAs (Surjective (𝟙 T.left))

lemma surjective_comp_left {T T' T'' : X.Etale} (π : T' ⟶ T) (π' : T'' ⟶ T')
    (h : Surjective π.left) (h' : Surjective π'.left) : Surjective (π' ≫ π).left := by
  change Surjective (π'.left ≫ π.left)
  infer_instance

end Scheme.Etale

namespace SplitEtaleHypercover

variable {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X] (U : SplitEtaleHypercover X)

/-- A compatible family of boundary simplices of degree `m` over `T` lifts to an `m`-simplex
after a surjective étale cover of `T`. -/
lemma exists_cover_lift (m : ℕ) {T : X.Etale}
    (p : ∀ Δ : SimplexCategory, Δ.len < m → (Δ ⟶ ⦋m⦌) → (T ⟶ U.simplicial.obj (op Δ)))
    (hp : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < m) (h' : Δ'.len < m) (α : Δ' ⟶ Δ)
      (θ : Δ ⟶ ⦋m⦌), p Δ h θ ≫ U.simplicial.map α.op = p Δ' h' (α ≫ θ)) :
    ∃ (T' : X.Etale) (π : T' ⟶ T) (s : T' ⟶ U.simplicial _⦋m⦌), Surjective π.left ∧
      ∀ (Δ : SimplexCategory) (h : Δ.len < m) (θ : Δ ⟶ ⦋m⦌),
        s ≫ U.simplicial.map θ.op = π ≫ p Δ h θ := by
  let G := Scheme.Etale.forget X
  obtain ⟨f, hf, -⟩ := U.matching_universal m (G.obj T) (fun Δ h θ ↦ G.map (p Δ h θ))
    (fun Δ Δ' h h' α θ ↦ by rw [← G.map_comp, hp])
  let f' : T ⟶ U.matching m := G.preimage f
  have := U.matching_cover m
  refine ⟨pullback f' (U.matchingMap m), pullback.fst _ _, pullback.snd _ _,
    Scheme.Etale.surjective_pullback_fst_left _ _, fun Δ h θ ↦ ?_⟩
  rw [← U.matchingMap_projection m Δ h θ, ← Category.assoc, ← pullback.condition,
    Category.assoc]
  congr 1
  apply G.map_injective
  rw [G.map_comp, Functor.map_preimage, hf]

/-- Finitely many conditions, each of which can be achieved after a surjective étale cover
(of any étale `T`-scheme), can be achieved simultaneously after one surjective étale cover. -/
lemma exists_cover_forall {T : X.Etale} {ι : Type*} {s : Set ι} (hs : s.Finite)
    (Q : ∀ {T' : X.Etale}, (T' ⟶ T) → ι → Prop)
    (hQ : ∀ {T' T'' : X.Etale} (π : T' ⟶ T) (π' : T'' ⟶ T') (i : ι), Q π i → Q (π' ≫ π) i)
    (hloc : ∀ i ∈ s, ∀ {T' : X.Etale} (π : T' ⟶ T),
      ∃ (T'' : X.Etale) (π' : T'' ⟶ T'), Surjective π'.left ∧ Q (π' ≫ π) i) :
    ∃ (T' : X.Etale) (π : T' ⟶ T), Surjective π.left ∧ ∀ i ∈ s, Q π i := by
  revert hloc
  induction s, hs using Set.Finite.induction_on with
  | empty => exact fun _ ↦ ⟨T, 𝟙 T, Scheme.Etale.surjective_id_left T, by simp⟩
  | @insert a s ha hs ih =>
    intro hloc
    obtain ⟨T₁, π₁, h₁, hQ₁⟩ := ih (fun i hi ↦ hloc i (Set.mem_insert_of_mem _ hi))
    obtain ⟨T₂, π₂, h₂, hQ₂⟩ := hloc a (Set.mem_insert _ _) π₁
    refine ⟨T₂, π₂ ≫ π₁, Scheme.Etale.surjective_comp_left _ _ h₁ h₂, ?_⟩
    rintro i (rfl | hi)
    · exact hQ₂
    · exact hQ _ _ _ (hQ₁ i hi)

/-- `h` is a cone with vertex `v`, defined over the cover `π : T' ⟶ T`, on the simplices of
the family `F` in degrees `< N`. -/
def IsCone (N : ℕ) {T T' : X.Etale} (π : T' ⟶ T) (F : ∀ k : ℕ, Set (T ⟶ U.simplicial _⦋k⦌))
    (v : T' ⟶ U.simplicial _⦋0⦌)
    (h : ∀ k : ℕ, (T ⟶ U.simplicial _⦋k⦌) → (T' ⟶ U.simplicial _⦋k + 1⦌)) : Prop :=
  (∀ k < N, ∀ τ ∈ F k, h k τ ≫ U.simplicial.δ 0 = π ≫ τ) ∧
  (0 < N → ∀ τ ∈ F 0, h 0 τ ≫ U.simplicial.δ 1 = v) ∧
  (∀ k, k + 1 < N → ∀ τ ∈ F (k + 1), ∀ i : Fin (k + 2),
    h (k + 1) τ ≫ U.simplicial.δ i.succ = h k (τ ≫ U.simplicial.δ i))

section cone

variable {U} {T : X.Etale} (F : ∀ k : ℕ, Set (T ⟶ U.simplicial _⦋k⦌))
  (hF : ∀ k, (F k).Finite)
  (hcl : ∀ k, ∀ τ ∈ F (k + 1), ∀ i : Fin (k + 2), τ ≫ U.simplicial.δ i ∈ F k)

include hF in
private lemma exists_cone_one {T₁ : X.Etale} (π₁ : T₁ ⟶ T) (v : T₁ ⟶ U.simplicial _⦋0⦌) :
    ∃ (T₂ : X.Etale) (π₂ : T₂ ⟶ T₁) (e : (T ⟶ U.simplicial _⦋0⦌) → (T₂ ⟶ U.simplicial _⦋1⦌)),
      Surjective π₂.left ∧ ∀ τ ∈ F 0, e τ ≫ U.simplicial.δ 0 = π₂ ≫ π₁ ≫ τ ∧
        e τ ≫ U.simplicial.δ 1 = π₂ ≫ v := by
  obtain ⟨T₂, π₂, hπ₂, hQ⟩ := U.exists_cover_forall (hF 0)
    (fun {T''} (π' : T'' ⟶ T₁) τ ↦ ∃ e : T'' ⟶ U.simplicial _⦋1⦌,
      e ≫ U.simplicial.δ 0 = π' ≫ π₁ ≫ τ ∧ e ≫ U.simplicial.δ 1 = π' ≫ v)
    (fun π π' τ ⟨e, he₀, he₁⟩ ↦ ⟨π' ≫ e, by simp [he₀], by simp [he₁]⟩)
    (by
      intro τ _ T' π'
      let x : Fin 2 → (T' ⟶ U.simplicial _⦋0⦌) := ![π' ≫ π₁ ≫ τ, π' ≫ v]
      obtain ⟨p, hp, hpx⟩ := U.simplicial.exists_boundary_extension x
        (U.simplicial.isBoundaryFamily_zero x)
      obtain ⟨T'', π'', s, hs, hsp⟩ := U.exists_cover_lift 1 p hp
      refine ⟨T'', π'', hs, s, ?_, ?_⟩
      · have := hsp _ (by simp) (SimplexCategory.δ 0)
        rw [hpx] at this
        simpa [x, SimplicialObject.δ] using this
      · have := hsp _ (by simp) (SimplexCategory.δ 1)
        rw [hpx] at this
        simpa [x, SimplicialObject.δ] using this)
  refine ⟨T₂, π₂, fun τ ↦ if hτ : τ ∈ F 0 then (hQ τ hτ).choose else
    π₂ ≫ π₁ ≫ τ ≫ U.simplicial.σ 0, hπ₂, fun τ hτ ↦ ?_⟩
  simp only [dif_pos hτ]
  exact (hQ τ hτ).choose_spec

include hF hcl in
private lemma exists_cone_succ (k : ℕ) {T₁ : X.Etale} (π₁ : T₁ ⟶ T)
    (v : T₁ ⟶ U.simplicial _⦋0⦌)
    (h : ∀ k : ℕ, (T ⟶ U.simplicial _⦋k⦌) → (T₁ ⟶ U.simplicial _⦋k + 1⦌))
    (hc : U.IsCone (k + 1) π₁ F v h) :
    ∃ (T₂ : X.Etale) (π₂ : T₂ ⟶ T₁)
      (e : (T ⟶ U.simplicial _⦋k + 1⦌) → (T₂ ⟶ U.simplicial _⦋k + 2⦌)),
      Surjective π₂.left ∧ ∀ τ ∈ F (k + 1), e τ ≫ U.simplicial.δ 0 = π₂ ≫ π₁ ≫ τ ∧
        ∀ i : Fin (k + 2), e τ ≫ U.simplicial.δ i.succ = π₂ ≫ h k (τ ≫ U.simplicial.δ i) := by
  obtain ⟨hc₁, hc₂, hc₃⟩ := hc
  obtain ⟨T₂, π₂, hπ₂, hQ⟩ := U.exists_cover_forall (hF (k + 1))
    (fun {T''} (π' : T'' ⟶ T₁) τ ↦ ∃ e : T'' ⟶ U.simplicial _⦋k + 2⦌,
      e ≫ U.simplicial.δ 0 = π' ≫ π₁ ≫ τ ∧
        ∀ i : Fin (k + 2), e ≫ U.simplicial.δ i.succ = π' ≫ h k (τ ≫ U.simplicial.δ i))
    (fun π π' τ ⟨e, he₀, he⟩ ↦ ⟨π' ≫ e, by simp [he₀], fun i ↦ by simp [he i]⟩)
    (by
      intro τ hτ T' π'
      let x : Fin (k + 3) → (T' ⟶ U.simplicial _⦋k + 1⦌) :=
        Fin.cases (π' ≫ π₁ ≫ τ) (fun i ↦ π' ≫ h k (τ ≫ U.simplicial.δ i))
      have hx : U.simplicial.IsBoundaryFamily x := by
        apply U.simplicial.isBoundaryFamily_succ
        intro i j hij
        induction i using Fin.cases with
        | zero =>
          simp only [x, Fin.cases_succ, Fin.castSucc_zero, Fin.cases_zero, Category.assoc,
            hc₁ k (Nat.lt_succ_self k) _ (hcl k τ hτ j)]
        | succ i =>
          induction j using Fin.cases with
          | zero => exact absurd hij (by simp [Fin.le_iff_val_le_val])
          | succ j =>
            have hij' : i ≤ j := Fin.succ_le_succ_iff.mp hij
            rw [← Fin.succ_castSucc]
            simp only [x, Fin.cases_succ, Category.assoc]
            congr 1
            cases k with
            | zero =>
              obtain rfl := Subsingleton.elim i 0
              obtain rfl := Subsingleton.elim j 0
              rw [hc₂ (Nat.succ_pos 0) _ (hcl 0 τ hτ _), hc₂ (Nat.succ_pos 0) _ (hcl 0 τ hτ _)]
            | succ k =>
              rw [hc₃ k (Nat.lt_succ_self _) _ (hcl _ τ hτ _),
                hc₃ k (Nat.lt_succ_self _) _ (hcl _ τ hτ _), Category.assoc, Category.assoc,
                SimplicialObject.δ_comp_δ _ hij']
      obtain ⟨p, hp, hpx⟩ := U.simplicial.exists_boundary_extension x hx
      obtain ⟨T'', π'', s, hs, hsp⟩ := U.exists_cover_lift (k + 2) p hp
      refine ⟨T'', π'', hs, s, ?_, fun i ↦ ?_⟩
      · have := hsp _ (by simp) (SimplexCategory.δ 0)
        rw [hpx] at this
        simpa [x, SimplicialObject.δ] using this
      · have := hsp _ (by simp) (SimplexCategory.δ i.succ)
        rw [hpx] at this
        simpa [x, SimplicialObject.δ] using this)
  refine ⟨T₂, π₂, fun τ ↦ if hτ : τ ∈ F (k + 1) then (hQ τ hτ).choose else
    π₂ ≫ π₁ ≫ τ ≫ U.simplicial.σ 0, hπ₂, fun τ hτ ↦ ?_⟩
  simp only [dif_pos hτ]
  exact (hQ τ hτ).choose_spec

include hF hcl in
/-- The local cone construction: after a surjective étale cover of `T`, the simplices of a
finite face-closed family `F` in degrees `< N` admit a cone. -/
theorem exists_cone (N : ℕ) :
    ∃ (T' : X.Etale) (π : T' ⟶ T) (v : T' ⟶ U.simplicial _⦋0⦌)
      (h : ∀ k : ℕ, (T ⟶ U.simplicial _⦋k⦌) → (T' ⟶ U.simplicial _⦋k + 1⦌)),
      Surjective π.left ∧ U.IsCone N π F v h := by
  induction N with
  | zero =>
    obtain ⟨T', π, v, hπ, -⟩ := U.exists_cover_lift 0
      (fun Δ h _ ↦ absurd h (Nat.not_lt_zero _)) (fun Δ _ h ↦ absurd h (Nat.not_lt_zero _))
    exact ⟨T', π, v, fun k τ ↦ π ≫ τ ≫ U.simplicial.σ 0, hπ,
      fun k hk ↦ absurd hk (Nat.not_lt_zero _), fun h ↦ absurd h (lt_irrefl 0),
      fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨T₁, π₁, v, h, hπ₁, hc⟩ := ih
    cases N with
    | zero =>
      obtain ⟨T₂, π₂, e, hπ₂, he⟩ := exists_cone_one F hF π₁ v
      refine ⟨T₂, π₂ ≫ π₁, π₂ ≫ v, Function.update (fun m τ ↦ π₂ ≫ h m τ) 0 e,
        Scheme.Etale.surjective_comp_left _ _ hπ₁ hπ₂, ?_, ?_, ?_⟩
      · intro m hm τ hτ
        obtain rfl : m = 0 := by omega
        simp only [Function.update_self, Category.assoc]
        exact (he τ hτ).1
      · intro _ τ hτ
        simp only [Function.update_self]
        exact (he τ hτ).2
      · intro m hm
        omega
    | succ k =>
      obtain ⟨T₂, π₂, e, hπ₂, he⟩ := exists_cone_succ F hF hcl k π₁ v h hc
      obtain ⟨hc₁, hc₂, hc₃⟩ := hc
      refine ⟨T₂, π₂ ≫ π₁, π₂ ≫ v, Function.update (fun m τ ↦ π₂ ≫ h m τ) (k + 1) e,
        Scheme.Etale.surjective_comp_left _ _ hπ₁ hπ₂, ?_, ?_, ?_⟩
      · intro m hm τ hτ
        rcases eq_or_ne m (k + 1) with rfl | hmk
        · simp only [Function.update_self, Category.assoc]
          exact (he τ hτ).1
        · simp only [Function.update_of_ne hmk, Category.assoc, hc₁ m (by omega) τ hτ]
      · intro _ τ hτ
        simp only [Function.update_of_ne (Nat.succ_ne_zero k).symm, Category.assoc,
          hc₂ (Nat.succ_pos k) τ hτ]
      · intro m hm τ hτ i
        rcases eq_or_ne m k with rfl | hmk
        · simp only [Function.update_self, Function.update_of_ne (Nat.succ_ne_self m).symm]
          exact (he τ hτ).2 i
        · have h₁ : m + 1 ≠ k + 1 := by omega
          have h₂ : m ≠ k + 1 := by omega
          simp only [Function.update_of_ne h₁, Function.update_of_ne h₂, Category.assoc,
            hc₃ m (by omega) τ hτ i]

end cone

end SplitEtaleHypercover

end AlgebraicGeometry
