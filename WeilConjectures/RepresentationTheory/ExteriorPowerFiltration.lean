/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import WeilConjectures.RepresentationTheory.CompositionSeries
public import WeilConjectures.Mathlib.RepresentationTheory.Basic

/-!
# The exterior powers of an extension

Let `A ⊆ M` be a submodule of a finite-dimensional vector space and `r ≥ 0`. The exterior power
`⋀^r M` has the decreasing filtration `P_j` spanned by the wedges `v₁ ∧ ⋯ ∧ v_r` with at least
`j` entries in `A`, and `P_j / P_{j + 1} ≅ ⋀^j A ⊗ ⋀^{r - j} (M / A)`. For a representation `ρ`
and a subrepresentation `A`, the `P_j` are subrepresentations of `⋀^r ρ` and these isomorphisms
are equivalences of representations. This is the two-step case of the blueprint lemma
`lem-mg-filtered-exterior-power`, from which the general case follows by induction on a
composition series.

The isomorphism is the map `a ⊗ b ↦ a ∧ σ(b)` for a linear section `σ` of `M → M / A`; it is
surjective onto `P_j / P_{j + 1}`, and it is bijective by the count
`∑_j C(dim A, j) C(dim M / A, r - j) = C(dim M, r)` (Vandermonde).

## Main definitions

- `exteriorPower.wedge`: the product `⋀^i M × ⋀^j M → ⋀^(i + j) M`.
- `exteriorPower.extFiltration`: the filtration `P_j` of `⋀^r M`.
- `Representation.exteriorPowerFiltration`: the filtration as subrepresentations.

## Main statements

- `Representation.nonempty_equiv_exteriorPowerFiltration`:
  `P_j / P_{j + 1} ≅ ⋀^j A ⊗ ⋀^{r - j} (M / A)` as representations.
-/

@[expose] public section

open scoped TensorProduct

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The exterior product `⋀^i M × ⋀^j M → ⋀^n M`, `n = i + j`, given by multiplication in the
exterior algebra. -/
noncomputable def wedge {i j n : ℕ} (h : i + j = n) :
    ⋀[R]^i M →ₗ[R] ⋀[R]^j M →ₗ[R] ⋀[R]^n M :=
  LinearMap.mk₂ R (fun x y ↦ ⟨x.1 * y.1, h ▸ SetLike.mul_mem_graded x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

theorem wedge_ιMulti {i j n : ℕ} (h : i + j = n) (a : Fin i → M) (b : Fin j → M) :
    wedge h (ιMulti R i a) (ιMulti R j b) = ιMulti R n (Fin.append a b ∘ Fin.cast h.symm) := by
  subst h
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti R i a * ExteriorAlgebra.ιMulti R j b =
    ExteriorAlgebra.ιMulti R (i + j) (Fin.append a b ∘ Fin.cast rfl)
  have : (fun k ↦ ExteriorAlgebra.ι R (Fin.append a b k)) =
      Fin.append (fun k ↦ ExteriorAlgebra.ι R (a k)) (fun k ↦ ExteriorAlgebra.ι R (b k)) := by
    funext k
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k <;> simp
  simp only [ExteriorAlgebra.ιMulti_apply, Function.comp_apply, Fin.cast_eq_self, this,
    List.ofFn_fin_append, List.prod_append]

variable (A : Submodule R M) (r : ℕ)

/-- The filtration of `⋀^r M` by the number of entries in a submodule `A`: `P_j` is spanned by
the wedges `v₁ ∧ ⋯ ∧ v_r` with at least `j` entries in `A`. -/
def extFiltration (j : ℕ) : Submodule R (⋀[R]^r M) :=
  Submodule.span R {x | ∃ (v : Fin r → M) (s : Finset (Fin r)), j ≤ s.card ∧ (∀ i ∈ s, v i ∈ A) ∧
    ιMulti R r v = x}

variable {A r}

theorem ιMulti_mem_extFiltration {j : ℕ} {v : Fin r → M} (s : Finset (Fin r)) (hs : j ≤ s.card)
    (hv : ∀ i ∈ s, v i ∈ A) : ιMulti R r v ∈ extFiltration A r j :=
  Submodule.subset_span ⟨v, s, hs, hv, rfl⟩

theorem extFiltration_antitone : Antitone (extFiltration A r) := fun _ _ hjj' ↦
  Submodule.span_mono fun _ ⟨v, s, hs, hv, hx⟩ ↦ ⟨v, s, hjj'.trans hs, hv, hx⟩

theorem extFiltration_zero : extFiltration A r 0 = ⊤ := by
  rw [eq_top_iff, ← ιMulti_span]
  exact Submodule.span_le.2 fun _ ⟨v, hv⟩ ↦ hv ▸ ιMulti_mem_extFiltration ∅ le_rfl (by simp)

theorem extFiltration_eq_bot {j : ℕ} (hj : r < j) : extFiltration A r j = ⊥ := by
  rw [extFiltration, Submodule.span_eq_bot]
  rintro _ ⟨v, s, hs, -, -⟩
  have := s.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-- An endomorphism `f` of `M` with `f(A) ⊆ A` preserves the filtration. -/
theorem map_extFiltration_le {f : M →ₗ[R] M} (hf : ∀ x ∈ A, f x ∈ A) (j : ℕ) :
    (extFiltration A r j).map (map r f) ≤ extFiltration A r j := by
  rw [extFiltration, Submodule.map_span_le]
  rintro _ ⟨v, s, hs, hv, rfl⟩
  rw [map_apply_ιMulti]
  exact ιMulti_mem_extFiltration s hs fun i hi ↦ hf _ (hv i hi)

/-- If `v` has at least `j` entries in `A`, on the positions `s`, and `w` agrees with `v` on `s`
and differs from `v` by elements of `A` elsewhere, then `v₁ ∧ ⋯ ∧ v_r` and `w₁ ∧ ⋯ ∧ w_r` agree
modulo `P_{j + 1}`. -/
theorem ιMulti_sub_mem_extFiltration {j : ℕ} {v w : Fin r → M} (s : Finset (Fin r))
    (hs : j ≤ s.card) (hv : ∀ i ∈ s, v i ∈ A) (hvw : ∀ i ∈ s, w i = v i)
    (hA : ∀ i, v i - w i ∈ A) : ιMulti R r v - ιMulti R r w ∈ extFiltration A r (j + 1) := by
  classical
  -- replace the entries outside `s` one by one
  let u : Finset (Fin r) → Fin r → M := fun D i ↦ if i ∈ D then w i else v i
  suffices h : ∀ D : Finset (Fin r), Disjoint D s →
      ιMulti R r v - ιMulti R r (u D) ∈ extFiltration A r (j + 1) by
    have h' := h sᶜ disjoint_compl_left
    convert h' using 3
    funext i
    by_cases hi : i ∈ s
    · simp [u, hi, hvw i hi]
    · simp [u, hi]
  intro D hD
  induction D using Finset.induction_on with
  | empty => simp [u]
  | insert a D ha ih =>
    have haS : a ∉ s := Finset.disjoint_left.1 hD (Finset.mem_insert_self a D)
    have hD' : Disjoint D s := Finset.disjoint_of_subset_left (Finset.subset_insert a D) hD
    have hu : u (insert a D) = Function.update (u D) a (w a) := by
      funext i
      by_cases hi : i = a
      · subst hi; simp [u]
      · simp [u, hi]
    have hu' : u D = Function.update (u D) a (v a) := by
      funext i
      by_cases hi : i = a
      · subst hi; simp [u, ha]
      · simp [Function.update_of_ne hi]
    have key : ιMulti R r (u D) - ιMulti R r (u (insert a D)) ∈ extFiltration A r (j + 1) := by
      have h₁ : ιMulti R r (u D) - ιMulti R r (u (insert a D)) =
          ιMulti R r (Function.update (u D) a (v a - w a)) := by
        rw [AlternatingMap.map_update_sub, ← hu', ← hu]
      rw [h₁]
      refine ιMulti_mem_extFiltration (insert a s) (by rw [Finset.card_insert_of_notMem haS]; omega)
        fun i hi ↦ ?_
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using hA i
      · have hia : i ≠ a := fun h ↦ haS (h ▸ hi)
        rw [Function.update_of_ne hia]
        have hiD : i ∉ D := fun h ↦ Finset.disjoint_left.1 hD' h hi
        simpa [u, hiD] using hv i hi
    have := Submodule.add_mem _ (ih hD') key
    rwa [sub_add_sub_cancel] at this


section Graded

variable (A) {j m : ℕ} (h : j + m = r) (σ : (M ⧸ A) →ₗ[R] M)

/-- The map `⋀^j A ⊗ ⋀^m (M ⧸ A) → ⋀^r M`, `a ⊗ b ↦ a ∧ σ(b)`, for a linear section `σ` of
`M → M ⧸ A` and `r = j + m`. -/
noncomputable def gradedLift : ⋀[R]^j A ⊗[R] ⋀[R]^m (M ⧸ A) →ₗ[R] ⋀[R]^r M :=
  TensorProduct.lift ((wedge h).compl₂ (map m σ) ∘ₗ map j A.subtype)

variable {A}

theorem gradedLift_tmul (a : Fin j → A) (b : Fin m → M ⧸ A) :
    gradedLift A h σ (ιMulti R j a ⊗ₜ ιMulti R m b) =
      ιMulti R r (Fin.append (A.subtype ∘ a) (σ ∘ b) ∘ Fin.cast h.symm) := by
  simp only [gradedLift, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compl₂_apply, map_apply_ιMulti, wedge_ιMulti]

/-- The positions of the first `j` entries of a tuple of length `r = j + m`. -/
def firstBlock : Finset (Fin r) :=
  Finset.univ.map ⟨fun i : Fin j ↦ Fin.cast h (Fin.castAdd m i), fun _ _ hi ↦ by simpa using hi⟩

theorem card_firstBlock : (firstBlock h).card = j := by
  simp [firstBlock]

theorem mem_firstBlock {i : Fin r} :
    i ∈ firstBlock h ↔ ∃ k : Fin j, Fin.cast h (Fin.castAdd m k) = i := by
  simp [firstBlock]

theorem append_cast_firstBlock {α : Type*} (x : Fin j → α) (y : Fin m → α) {i : Fin r}
    (hi : i ∈ firstBlock h) : ∃ k, (Fin.append x y ∘ Fin.cast h.symm) i = x k := by
  obtain ⟨k, rfl⟩ := (mem_firstBlock h).1 hi
  exact ⟨k, by simp⟩

theorem append_cast_not_firstBlock {α : Type*} (x : Fin j → α) (y : Fin m → α) {i : Fin r}
    (hi : i ∉ firstBlock h) : ∃ k, (Fin.append x y ∘ Fin.cast h.symm) i = y k := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ : (∃ k : Fin j, Fin.cast h.symm i = Fin.castAdd m k) ∨
      ∃ k : Fin m, Fin.cast h.symm i = Fin.natAdd j k := by
    refine Fin.addCases (motive := fun t ↦ (∃ k : Fin j, t = Fin.castAdd m k) ∨
      ∃ k : Fin m, t = Fin.natAdd j k) (fun k ↦ Or.inl ⟨k, rfl⟩) (fun k ↦ Or.inr ⟨k, rfl⟩) _
  · exact absurd ((mem_firstBlock h).2 ⟨k, by rw [← hk]; simp⟩) hi
  · exact ⟨k, by simp [hk]⟩

/-- The image of `gradedLift` lies in `P_j`. -/
theorem gradedLift_mem_extFiltration (t : ⋀[R]^j A ⊗[R] ⋀[R]^m (M ⧸ A)) :
    gradedLift A h σ t ∈ extFiltration A r j := by
  suffices (extFiltration A r j).mkQ ∘ₗ gradedLift A h σ = 0 by
    simpa using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this t)
  ext a b
  change (extFiltration A r j).mkQ (gradedLift A h σ (ιMulti R j a ⊗ₜ ιMulti R m b)) = 0
  rw [gradedLift_tmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ιMulti_mem_extFiltration (firstBlock h) (card_firstBlock h).ge fun i hi ↦ ?_
  obtain ⟨k, hk⟩ := append_cast_firstBlock h (A.subtype ∘ a) (σ ∘ b) hi
  rw [hk]
  exact (a k).2


/-- The induced map `⋀^j A ⊗ ⋀^m (M ⧸ A) → P_j / P_{j + 1}`. -/
noncomputable def gradedMap : ⋀[R]^j A ⊗[R] ⋀[R]^m (M ⧸ A) →ₗ[R]
    extFiltration A r j ⧸ (extFiltration A r (j + 1)).comap (extFiltration A r j).subtype :=
  Submodule.mkQ _ ∘ₗ (gradedLift A h σ).codRestrict _ (gradedLift_mem_extFiltration h σ)

theorem gradedMap_apply (t : ⋀[R]^j A ⊗[R] ⋀[R]^m (M ⧸ A)) :
    gradedMap h σ t =
      Submodule.Quotient.mk ⟨gradedLift A h σ t, gradedLift_mem_extFiltration h σ t⟩ :=
  rfl

/-- Two elements `x, y` of `P_j` have the same image in `P_j / P_{j + 1}` exactly when
`x - y ∈ P_{j + 1}`. -/
theorem mk_eq_mk_iff {j : ℕ} (x y : extFiltration A r j) :
    (Submodule.Quotient.mk x : extFiltration A r j ⧸
      (extFiltration A r (j + 1)).comap (extFiltration A r j).subtype) =
        Submodule.Quotient.mk y ↔ (x : ⋀[R]^r M) - y ∈ extFiltration A r (j + 1) :=
  Submodule.Quotient.eq _

variable {σ} (hσ : A.mkQ ∘ₗ σ = LinearMap.id)
include hσ

theorem sub_section_mem (x : M) : x - σ (A.mkQ x) ∈ A := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub,
    ← LinearMap.comp_apply A.mkQ σ, hσ, LinearMap.id_apply, sub_self]

/-- Every element of `P_j` agrees modulo `P_{j + 1}` with an element of the image of
`gradedLift`: a generating wedge with entries in `A` at the positions `s`, `#s ≥ j`, is up to
sign the wedge of `j` entries of `A` and of `m` further entries, which may be replaced by their
images under `σ ∘ (M → M ⧸ A)` modulo `P_{j + 1}`. -/
theorem exists_gradedLift_sub_mem {x : ⋀[R]^r M} (hx : x ∈ extFiltration A r j) :
    ∃ t, gradedLift A h σ t - x ∈ extFiltration A r (j + 1) := by
  induction hx using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := hy
    refine ⟨t + t', ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ ht ht'
  | smul c x _ hx =>
    obtain ⟨t, ht⟩ := hx
    refine ⟨c • t, ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ c ht
  | mem x hx =>
    obtain ⟨v, s, hs, hv, rfl⟩ := hx
    obtain ⟨s', hs's, hs'⟩ := Finset.exists_subset_card_eq hs
    have hc : s'ᶜ.card = m := by
      rw [Finset.card_compl, Fintype.card_fin, hs']
      omega
    let f := s'.orderEmbOfFin hs'
    let g := s'ᶜ.orderEmbOfFin hc
    let φ : Fin (j + m) → Fin r := Fin.append f g
    have hinj : Function.Injective φ := Fin.append_injective_iff.2 ⟨f.injective, g.injective,
      fun a b hab ↦ (Finset.mem_compl.1 (s'ᶜ.orderEmbOfFin_mem hc b))
        (hab ▸ s'.orderEmbOfFin_mem hs' a)⟩
    have hbij : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, by simp [h]⟩
    let π : Equiv.Perm (Fin r) := (finCongr h).symm.trans (Equiv.ofBijective φ hbij)
    have hvπ : v ∘ π = Fin.append (v ∘ f) (v ∘ g) ∘ Fin.cast h.symm := by
      funext i
      simp only [Function.comp_apply, π, Equiv.trans_apply, Equiv.ofBijective_apply, φ,
        finCongr_symm, finCongr_apply]
      refine Fin.addCases (motive := fun k ↦ v (Fin.append f g k) =
        Fin.append (v ∘ f) (v ∘ g) k) (fun k ↦ ?_) (fun k ↦ ?_) (Fin.cast h.symm i) <;> simp
    let a : Fin j → A := fun i ↦ ⟨v (f i), hv _ (hs's (s'.orderEmbOfFin_mem hs' i))⟩
    let b : Fin m → M ⧸ A := A.mkQ ∘ v ∘ g
    let c : R := ((Equiv.Perm.sign π : ℤ) : R)
    have hc : c * c = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    refine ⟨c • (ιMulti R j a ⊗ₜ ιMulti R m b), ?_⟩
    have hperm : ιMulti R r v = c • ιMulti R r (v ∘ π) := by
      rw [AlternatingMap.map_perm, Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul, hc,
        one_smul]
    rw [map_smul, gradedLift_tmul, hperm, hvπ, ← smul_sub]
    refine Submodule.smul_mem _ _ ?_
    rw [← neg_mem_iff, neg_sub]
    refine ιMulti_sub_mem_extFiltration (firstBlock h) (card_firstBlock h).ge
      (fun i hi ↦ ?_) (fun i hi ↦ ?_) fun i ↦ ?_
    · obtain ⟨k, hk⟩ := append_cast_firstBlock h (v ∘ f) (v ∘ g) hi
      rw [hk]
      exact (a k).2
    · obtain ⟨k, rfl⟩ := (mem_firstBlock h).1 hi
      simp [a]
    · by_cases hi : i ∈ firstBlock h
      · obtain ⟨k, rfl⟩ := (mem_firstBlock h).1 hi
        simp [a]
      · obtain ⟨k, rfl⟩ | ⟨k, hk⟩ : (∃ k : Fin j, Fin.cast h (Fin.castAdd m k) = i) ∨
            ∃ k : Fin m, Fin.cast h.symm i = Fin.natAdd j k := by
          refine Fin.addCases (motive := fun t ↦ (∃ k : Fin j, Fin.cast h (Fin.castAdd m k) =
            Fin.cast h t) ∨ ∃ k : Fin m, t = Fin.natAdd j k) (fun k ↦ Or.inl ⟨k, rfl⟩)
            (fun k ↦ Or.inr ⟨k, rfl⟩) (Fin.cast h.symm i) |>.imp (fun ⟨k, hk⟩ ↦ ⟨k, by simpa
            using hk⟩) id
        · exact absurd ((mem_firstBlock h).2 ⟨k, rfl⟩) hi
        · simp only [Function.comp_apply, hk, Fin.append_right, b]
          exact sub_section_mem hσ _

/-- The map `⋀^j A ⊗ ⋀^m (M ⧸ A) → P_j / P_{j + 1}` is surjective. -/
theorem gradedMap_surjective : Function.Surjective (gradedMap h σ) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x
  obtain ⟨t, ht⟩ := exists_gradedLift_sub_mem h hσ x.2
  exact ⟨t, (mk_eq_mk_iff _ _).2 ht⟩

/-- `gradedLift` is compatible, modulo `P_{j + 1}`, with an endomorphism `f` of `M` preserving
`A`, acting on `⋀^j A ⊗ ⋀^m (M ⧸ A)` through its restriction to `A` and the induced map on
`M ⧸ A`. -/
theorem map_gradedLift_sub_mem (f : M →ₗ[R] M) (hf : ∀ x ∈ A, f x ∈ A)
    (t : ⋀[R]^j A ⊗[R] ⋀[R]^m (M ⧸ A)) :
    map r f (gradedLift A h σ t) - gradedLift A h σ (TensorProduct.map (map j (f.restrict hf))
      (map m (A.mapQ A f hf)) t) ∈ extFiltration A r (j + 1) := by
  suffices (extFiltration A r (j + 1)).mkQ ∘ₗ (map r f ∘ₗ gradedLift A h σ -
      gradedLift A h σ ∘ₗ TensorProduct.map (map j (f.restrict hf)) (map m (A.mapQ A f hf))) = 0 by
    simpa using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this t)
  ext a b
  change (extFiltration A r (j + 1)).mkQ (map r f (gradedLift A h σ (ιMulti R j a ⊗ₜ ιMulti R m b))
    - gradedLift A h σ (TensorProduct.map (map j (f.restrict hf)) (map m (A.mapQ A f hf))
      (ιMulti R j a ⊗ₜ ιMulti R m b))) = 0
  rw [TensorProduct.map_tmul, map_apply_ιMulti, map_apply_ιMulti, gradedLift_tmul,
    gradedLift_tmul, map_apply_ιMulti, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ιMulti_sub_mem_extFiltration (firstBlock h) (card_firstBlock h).ge
    (fun i hi ↦ ?_) (fun i hi ↦ ?_) fun i ↦ ?_
  · obtain ⟨k, rfl⟩ := (mem_firstBlock h).1 hi
    simpa using hf _ (a k).2
  · obtain ⟨k, rfl⟩ := (mem_firstBlock h).1 hi
    simp
  · refine Fin.addCases (motive := fun t ↦ (f ∘ Fin.append (A.subtype ∘ a) (σ ∘ b)) t -
      Fin.append (A.subtype ∘ (f.restrict hf ∘ a)) (σ ∘ (A.mapQ A f hf ∘ b)) t ∈ A)
      (fun k ↦ ?_) (fun k ↦ ?_) (Fin.cast h.symm i)
    · simp
    · simp only [Function.comp_apply, Fin.append_right]
      have h₁ := sub_section_mem hσ (f (σ (b k)))
      have hb : A.mkQ (σ (b k)) = b k := LinearMap.congr_fun hσ (b k)
      have h₂ : A.mkQ (f (σ (b k))) = A.mapQ A f hf (b k) :=
        calc A.mkQ (f (σ (b k))) = A.mapQ A f hf (A.mkQ (σ (b k))) := rfl
          _ = A.mapQ A f hf (b k) := by rw [hb]
      rwa [h₂] at h₁
end Graded


section Dimension

variable {K V X : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X] [Module K X]
  [FiniteDimensional K X]

/-- The dimensions of the steps `P j / P (j + 1)` of a decreasing chain of subspaces add up to
`dim P 0 - dim P N`. -/
theorem sum_finrank_quotient_add_finrank (P : ℕ → Submodule K X) (hP : Antitone P) (N : ℕ) :
    ∑ j ∈ Finset.range N, Module.finrank K (P j ⧸ (P (j + 1)).comap (P j).subtype) +
      Module.finrank K (P N) = Module.finrank K (P 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, ← ih]
    congr 1
    have h := Submodule.finrank_quotient_add_finrank ((P (N + 1)).comap (P N).subtype)
    rwa [(Submodule.comapSubtypeEquivOfLe (hP (Nat.le_succ N))).finrank_eq] at h

variable [FiniteDimensional K V] {A : Submodule K V} {σ : (V ⧸ A) →ₗ[K] V}
  (hσ : A.mkQ ∘ₗ σ = LinearMap.id) {r : ℕ}
include hσ

/-- The map `⋀^j A ⊗ ⋀^{r - j} (V ⧸ A) → P_j / P_{j + 1}` is bijective, for `j ≤ r`: it is
surjective, and the dimensions agree since
`∑_j C(dim A, j) C(dim V ⧸ A, r - j) = C(dim V, r)`. -/
theorem gradedMap_bijective {j : ℕ} (hj : j ≤ r) :
    Function.Bijective (gradedMap (A := A) (Nat.add_sub_cancel' hj) σ) := by
  let src : ℕ → ℕ := fun j ↦ Module.finrank K (⋀[K]^j A ⊗[K] ⋀[K]^(r - j) (V ⧸ A))
  let tgt : ℕ → ℕ := fun j ↦ Module.finrank K (extFiltration A r j ⧸
    (extFiltration A r (j + 1)).comap (extFiltration A r j).subtype)
  have hle : ∀ j ∈ Finset.range (r + 1), tgt j ≤ src j := fun j hj ↦ by
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h := LinearMap.finrank_range_le (gradedMap (A := A) (Nat.add_sub_cancel' hjr) σ)
    rwa [LinearMap.range_eq_top.2 (gradedMap_surjective _ hσ), finrank_top] at h
  have hsrc : ∑ j ∈ Finset.range (r + 1), src j = (Module.finrank K V).choose r := by
    simp only [src, Module.finrank_tensorProduct, exteriorPower.finrank_eq]
    rw [← Submodule.finrank_quotient_add_finrank A, add_comm (Module.finrank K (V ⧸ A)),
      Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k ↦ (Module.finrank K A).choose i *
        (Module.finrank K (V ⧸ A)).choose k)]
  have htgt : ∑ j ∈ Finset.range (r + 1), tgt j = (Module.finrank K V).choose r := by
    have h := sum_finrank_quotient_add_finrank (extFiltration A r) extFiltration_antitone (r + 1)
    rw [extFiltration_eq_bot (Nat.lt_succ_self r), finrank_bot, add_zero, extFiltration_zero,
      finrank_top, exteriorPower.finrank_eq] at h
    exact h
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (htgt.trans hsrc.symm) j
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).2
    (gradedMap_surjective _ hσ), gradedMap_surjective _ hσ⟩

end Dimension
end exteriorPower
