/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.Constituents

/-!
# Graded pieces of finite filtrations of representations

Let `ρ` be a representation of a group `W` on a `k`-vector space `V`. A *finite filtration* of `ρ`
is a chain `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = V` of subrepresentations, with *graded pieces* `F_{i+1} / F_i`.
`Representation.HasGradedPieces ρ P` says that `ρ` has a finite filtration whose graded pieces, in a
suitable order, satisfy the properties `P i`, each index `i` occurring exactly once. The typical
property is `Representation.EquivTo τ`, being equivalent to a fixed representation `τ`.

The main result is the refinement of filtrations (`Representation.HasGradedPieces.trans`): if
the graded pieces of a filtration have filtrations of their own, these refine the first one.

## Main definitions

- `Representation.RepProp`: a property of representations.
- `Representation.EquivTo`: the property of being equivalent to a fixed representation.
- `Representation.HasGradedPieces`: `ρ` has a finite filtration with graded pieces satisfying a
  family of properties.

## Main results

- `Representation.HasGradedPieces.append`: filtrations of a subrepresentation and of the quotient
  combine.
- `Representation.HasGradedPieces.trans`: refinement of a filtration by filtrations of its graded
  pieces.
- `Representation.CompositionSeries.hasGradedPieces`: a composition series is a filtration whose
  graded pieces are its composition factors.
-/

@[expose] public section

universe u v w

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- Equal subrepresentations have equivalent subquotients. -/
noncomputable def subquotientCongr {S S' U U' : Subrepresentation ρ} (hS : S = S') (hU : U = U') :
    (S.subquotient U).Equiv (S'.subquotient U') := by
  subst hS hU
  exact .refl _

/-- For `U, S ≤ A`, the subquotient `S / U` computed inside `A` is the subquotient `S / U`. -/
noncomputable def subquotientComapSubtypeEquiv {A S U : Subrepresentation ρ} (hS : S ≤ A) :
    ((comap A.subtype S).subquotient (comap A.subtype U)).Equiv (S.subquotient U) :=
  subquotientEquivOfIntertwiningMap A.subtype (fun _ hx ↦ hx) (fun _ _ hx ↦ hx)
    (fun _ _ hx ↦ hx) fun y hy ↦ ⟨⟨y, hS hy⟩, hy, by
      change y - y ∈ U
      rw [sub_self]
      exact U.toSubmodule.zero_mem⟩

/-- For a subrepresentation `A`, the subquotient `S / U` of `ρ`, for `U ≤ S ≤ A`... computed via the
images in `ρ` of subrepresentations of `A`: `A(S) / A(U) ≃ S / U`. -/
noncomputable def subquotientMapSubtypeEquiv {A : Subrepresentation ρ}
    (S U : Subrepresentation A.toRepresentation) :
    ((map A.subtype S).subquotient (map A.subtype U)).Equiv (S.subquotient U) :=
  (subquotientEquivOfIntertwiningMap A.subtype (U := U) (S := S) (U' := map A.subtype U)
    (S' := map A.subtype S) (fun x hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ by
      obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
      exact (A.subtype_injective hyx) ▸ hy)
    fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
      exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩).symm

/-- The quotient `V ⧸ P` is the subquotient `⊤ / P`. -/
noncomputable def quotientEquivTopSubquotient (P : Subrepresentation ρ) :
    P.quotient.Equiv ((⊤ : Subrepresentation ρ).subquotient P) :=
  .mk (Submodule.Quotient.equiv _ _ Submodule.topEquiv.symm (by
      ext x
      simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_comap,
        Submodule.subtype_apply]
      rfl)) fun _ ↦ Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl)

theorem comap_subtype_bot (A : Subrepresentation ρ) : comap A.subtype ⊥ = ⊥ :=
  toSubmodule_injective (by
    change Submodule.comap A.toSubmodule.subtype ⊥ = ⊥
    rw [Submodule.comap_bot, Submodule.ker_subtype])

theorem comap_subtype_self (A : Subrepresentation ρ) : comap A.subtype A = ⊤ :=
  toSubmodule_injective (Submodule.comap_subtype_self _)

theorem map_subtype_bot (A : Subrepresentation ρ) :
    map A.subtype (⊥ : Subrepresentation A.toRepresentation) = ⊥ :=
  toSubmodule_injective (Submodule.map_bot _)

theorem map_subtype_top (A : Subrepresentation ρ) :
    map A.subtype (⊤ : Subrepresentation A.toRepresentation) = A :=
  toSubmodule_injective (by
    change Submodule.map A.toSubmodule.subtype ⊤ = A.toSubmodule
    rw [Submodule.map_top, Submodule.range_subtype])

theorem comap_mkQ_bot (P : Subrepresentation ρ) : comap P.mkQ ⊥ = P :=
  toSubmodule_injective (by
    change Submodule.comap P.toSubmodule.mkQ ⊥ = P.toSubmodule
    rw [Submodule.comap_bot, Submodule.ker_mkQ])

theorem comap_mkQ_top (P : Subrepresentation ρ) : comap P.mkQ ⊤ = ⊤ :=
  toSubmodule_injective (Submodule.comap_top _)

end Subrepresentation

namespace Representation

variable (k : Type u) [Field k] (W : Type w) [Group W]

/-- A property of representations of `W` on `k`-vector spaces in the universe `v`, such as being
equivalent to a fixed representation (`Representation.EquivTo`). -/
def RepProp :=
  ∀ {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y}, Representation k W Y → Prop

variable {k W}

/-- The property of being equivalent to the representation `τ`. -/
def EquivTo {X : Type*} [AddCommGroup X] [Module k X] (τ : Representation k W X) :
    RepProp.{u, v} k W :=
  fun {_} {_} {_} σ ↦ Nonempty (σ.Equiv τ)

/-- A property of representations is *invariant* if it is preserved by equivalences. -/
def RepProp.IsInvariant (P : RepProp.{u, v} k W) : Prop :=
  ∀ {Y Y' : Type v} {_ : AddCommGroup Y} {_ : Module k Y} {_ : AddCommGroup Y'} {_ : Module k Y'}
    {σ : Representation k W Y} {σ' : Representation k W Y'}, σ.Equiv σ' → P σ → P σ'

theorem isInvariant_equivTo {X : Type*} [AddCommGroup X] [Module k X]
    (τ : Representation k W X) : RepProp.IsInvariant (EquivTo.{u, v} τ) :=
  fun e ⟨f⟩ ↦ ⟨e.symm.trans f⟩

/-- `ρ` *has graded pieces* `P`: there is a finite filtration `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = V` by
subrepresentations and a bijection `e : Fin m ≃ ι` such that the graded piece `F_{i+1} / F_i`
satisfies `P (e i)`. So the graded pieces, in a suitable order, satisfy the properties `P i`, each
index `i` occurring exactly once. -/
def HasGradedPieces {V : Type v} [AddCommGroup V] [Module k V] (ρ : Representation k W V)
    {ι : Type*} (P : ι → RepProp.{u, v} k W) : Prop :=
  ∃ (m : ℕ) (F : Fin (m + 1) → Subrepresentation ρ) (e : Fin m ≃ ι), Monotone F ∧ F 0 = ⊥ ∧
    F (Fin.last m) = ⊤ ∧ ∀ i : Fin m, P (e i) ((F i.succ).subquotient (F i.castSucc))

namespace HasGradedPieces

variable {V V' : Type v} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  {ρ : Representation k W V} {σ : Representation k W V'} {ι κ : Type*}
  {P Q : ι → RepProp.{u, v} k W}

theorem mono (h : HasGradedPieces ρ P)
    (hPQ : ∀ i {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y} (τ : Representation k W Y),
      P i τ → Q i τ) : HasGradedPieces ρ Q := by
  obtain ⟨m, F, e, hF, h0, hl, hP⟩ := h
  exact ⟨m, F, e, hF, h0, hl, fun i ↦ hPQ _ _ (hP i)⟩

/-- Reindexing the graded pieces along a bijection. -/
theorem reindex (h : HasGradedPieces ρ P) (f : ι ≃ κ) :
    HasGradedPieces ρ fun j ↦ P (f.symm j) := by
  obtain ⟨m, F, e, hF, h0, hl, hP⟩ := h
  exact ⟨m, F, e.trans f, hF, h0, hl, fun i ↦ by simpa using hP i⟩

/-- Graded pieces along an equivalence of representations. -/
theorem of_equiv (h : HasGradedPieces ρ P) (hP : ∀ i, RepProp.IsInvariant (P i)) (f : ρ.Equiv σ) :
    HasGradedPieces σ P := by
  obtain ⟨m, F, e, hF, h0, hl, hPF⟩ := h
  let O := Subrepresentation.orderIsoMapComap f
  refine ⟨m, fun i ↦ O (F i), e, O.monotone.comp hF, by simp [h0], by simp [hl],
    fun i ↦ hP _ (Subrepresentation.subquotientEquiv f _ _) (hPF i)⟩

/-- A representation is a filtration with one graded piece, itself. -/
theorem single {P : RepProp.{u, v} k W} (hP : RepProp.IsInvariant P) (h : P ρ) :
    HasGradedPieces ρ fun _ : Unit ↦ P := by
  refine ⟨1, ![⊥, ⊤], Equiv.equivPUnit _, fun i j hij ↦ ?_, rfl, rfl, fun i ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i
    exact hP (Subrepresentation.topSubquotientBotEquiv ρ).symm h

/-- The zero representation is a filtration without graded pieces. -/
theorem of_subsingleton [Subsingleton V] {P : PEmpty → RepProp.{u, v} k W} :
    HasGradedPieces ρ P := by
  have htop : (⊤ : Subrepresentation ρ) = ⊥ :=
    Subrepresentation.toSubmodule_injective (Submodule.eq_bot_of_subsingleton)
  refine ⟨0, fun _ ↦ ⊥, Equiv.equivPEmpty _, fun _ _ _ ↦ le_rfl, rfl, htop.symm, fun i ↦ ?_⟩
  exact i.elim0


/-- **Concatenating filtrations.** Filtrations of a subrepresentation `A` and of the quotient
`V ⧸ A` combine to a filtration of `V`, with the graded pieces of both. -/
theorem append (A : Subrepresentation ρ) {ι₁ ι₂ : Type*} {P₁ : ι₁ → RepProp.{u, v} k W}
    {P₂ : ι₂ → RepProp.{u, v} k W} (hP₁ : ∀ i, RepProp.IsInvariant (P₁ i))
    (hP₂ : ∀ i, RepProp.IsInvariant (P₂ i)) (h₁ : HasGradedPieces A.toRepresentation P₁)
    (h₂ : HasGradedPieces A.quotient P₂) : HasGradedPieces ρ (Sum.elim P₁ P₂) := by
  obtain ⟨m₁, F₁, e₁, hF₁, h0₁, hl₁, hPF₁⟩ := h₁
  obtain ⟨m₂, F₂, e₂, hF₂, h0₂, hl₂, hPF₂⟩ := h₂
  let G : ℕ → Subrepresentation ρ := fun n ↦ if h : n ≤ m₁ then
    Subrepresentation.map A.subtype (F₁ ⟨n, by omega⟩) else
    Subrepresentation.comap A.mkQ (F₂ ⟨min (n - m₁) m₂, by omega⟩)
  have hG₁ (n : ℕ) (hn : n ≤ m₁) :
      G n = Subrepresentation.map A.subtype (F₁ ⟨n, by omega⟩) := dif_pos hn
  have hG₂ (n : ℕ) (hn₁ : m₁ ≤ n) (hn₂ : n ≤ m₁ + m₂) :
      G n = Subrepresentation.comap A.mkQ (F₂ ⟨n - m₁, by omega⟩) := by
    rcases hn₁.lt_or_eq with hn₁ | rfl
    · rw [show G n = _ from dif_neg (by omega)]
      congr 2
      ext
      exact min_eq_left (by omega)
    · rw [hG₁ m₁ le_rfl, show (⟨m₁, _⟩ : Fin (m₁ + 1)) = Fin.last m₁ from rfl, hl₁,
        Subrepresentation.map_subtype_top, show (⟨m₁ - m₁, _⟩ : Fin (m₂ + 1)) = 0 from
          Fin.ext (Nat.sub_self m₁), h0₂, Subrepresentation.comap_mkQ_bot]
  have hGA (n : ℕ) (hn : n ≤ m₁) : G n ≤ A := by
    rw [hG₁ n hn]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAG (n : ℕ) (hn₁ : m₁ ≤ n) (hn₂ : n ≤ m₁ + m₂) : A ≤ G n := by
    rw [hG₂ n hn₁ hn₂]
    intro x hx
    rw [Subrepresentation.mem_comap]
    have h0 : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [h0]
    exact Submodule.zero_mem _
  refine ⟨m₁ + m₂, fun n ↦ G n, finSumFinEquiv.symm.trans (e₁.sumCongr e₂), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    change G a ≤ G b
    have hab' : (a : ℕ) ≤ b := hab
    by_cases ha : (a : ℕ) ≤ m₁
    · by_cases hb : (b : ℕ) ≤ m₁
      · rw [hG₁ _ ha, hG₁ _ hb]
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hF₁ (show (⟨a, _⟩ : Fin (m₁ + 1)) ≤ ⟨b, _⟩ from hab') hx, rfl⟩
      · exact (hGA _ ha).trans (hAG _ (by omega) (by omega))
    · rw [hG₂ _ (by omega) (by omega), hG₂ _ (by omega) (by omega)]
      intro x hx
      exact hF₂ (show (⟨a - m₁, _⟩ : Fin (m₂ + 1)) ≤ ⟨b - m₁, _⟩ from
        (by simp only [Fin.mk_le_mk]; omega)) hx
  · change G 0 = ⊥
    rw [hG₁ 0 (Nat.zero_le _), show (⟨0, _⟩ : Fin (m₁ + 1)) = 0 from rfl, h0₁,
      Subrepresentation.map_subtype_bot]
  · change G (m₁ + m₂) = ⊤
    rw [hG₂ _ (by omega) le_rfl, show (⟨m₁ + m₂ - m₁, _⟩ : Fin (m₂ + 1)) = Fin.last m₂ from
      Fin.ext (by simp), hl₂, Subrepresentation.comap_mkQ_top]
  · intro k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · have he : (finSumFinEquiv.symm.trans (e₁.sumCongr e₂)) (Fin.castAdd m₂ i) =
          .inl (e₁ i) := by
        simp
      rw [he]
      refine hP₁ _ ((Subrepresentation.subquotientMapSubtypeEquiv _ _).symm.trans
        (Subrepresentation.subquotientCongr ?_ ?_).symm) (hPF₁ i)
      · change G _ = _
        rw [hG₁ _ (by simp)]
        congr 2
      · change G _ = _
        rw [hG₁ _ (by simp)]
        congr 2
    · have he : (finSumFinEquiv.symm.trans (e₁.sumCongr e₂)) (Fin.natAdd m₁ j) =
          .inr (e₂ j) := by
        simp
      rw [he]
      refine hP₂ _ ((Subrepresentation.subquotientComapEquiv A.mkQ A.mkQ_surjective _ _).symm.trans
        (Subrepresentation.subquotientCongr ?_ ?_).symm) (hPF₂ j)
      · change G _ = _
        rw [hG₂ _ (by simp; omega) (by simp)]
        congr 2
        ext
        simp; omega
      · change G _ = _
        rw [hG₂ _ (by simp) (by simp)]
        congr 2
        ext
        simp

/-- The indices `Σ i : Fin (m + 1), κ i` split into those over `Fin m` and those over the last
index. -/
private def sigmaFinSuccEquiv {m : ℕ} (κ : Fin (m + 1) → Type*) :
    (Σ j : Fin m, κ j.castSucc) ⊕ κ (Fin.last m) ≃ Σ i : Fin (m + 1), κ i where
  toFun := Sum.elim (fun x ↦ ⟨x.1.castSucc, x.2⟩) fun y ↦ ⟨Fin.last m, y⟩
  invFun x := Fin.lastCases (motive := fun i ↦ κ i → _) (fun y ↦ .inr y)
    (fun j y ↦ .inl ⟨j, y⟩) x.1 x.2
  left_inv x := by
    rcases x with ⟨j, y⟩ | y <;> simp
  right_inv := by
    rintro ⟨i, y⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp

/-- Refinement of a filtration whose graded pieces, indexed by `Fin m`, have filtrations. -/
private theorem trans_aux : ∀ (m : ℕ)
    {V : Type v} [AddCommGroup V] [Module k V] (ρ : Representation k W V)
    (F : Fin (m + 1) → Subrepresentation ρ) (_ : Monotone F) (_ : F 0 = ⊥)
    (_ : F (Fin.last m) = ⊤) (κ : Fin m → Type*) (R : ∀ i, κ i → RepProp.{u, v} k W)
    (_ : ∀ i j, RepProp.IsInvariant (R i j))
    (_ : ∀ i, HasGradedPieces ((F i.succ).subquotient (F i.castSucc)) (R i)),
    HasGradedPieces ρ fun x : Σ i, κ i ↦ R x.1 x.2
  | 0, V, _, _, ρ, F, _, h0, hl, κ, R, _, _ =>
    ⟨0, F, Equiv.equivOfIsEmpty _ _,
      fun a b _ ↦ by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b], h0, hl, fun i ↦ i.elim0⟩
  | m + 1, V, _, _, ρ, F, hF, h0, hl, κ, R, hR, h => by
    -- the subrepresentation `A = F m` and the restriction of the filtration to it
    let A := F (Fin.last m).castSucc
    let F' : Fin (m + 1) → Subrepresentation A.toRepresentation :=
      fun j ↦ Subrepresentation.comap A.subtype (F j.castSucc)
    have hFA (j : Fin (m + 1)) : F j.castSucc ≤ A := hF (Fin.castSucc_le_castSucc_iff.2 j.le_last)
    have h₁ := trans_aux m A.toRepresentation F'
      (fun a b hab x hx ↦ hF (Fin.castSucc_le_castSucc_iff.2 hab) hx)
      (by simp only [F', Fin.castSucc_zero, h0, Subrepresentation.comap_subtype_bot])
      (Subrepresentation.comap_subtype_self A) (fun j ↦ κ j.castSucc) (fun j ↦ R j.castSucc)
      (fun _ _ ↦ hR _ _) fun j ↦ (h j.castSucc).of_equiv (fun _ ↦ hR _ _)
        (Subrepresentation.subquotientComapSubtypeEquiv (hFA j.succ)).symm
    have h₂ : HasGradedPieces A.quotient (R (Fin.last m)) :=
      (h (Fin.last m)).of_equiv (fun _ ↦ hR _ _)
        ((Subrepresentation.subquotientCongr hl rfl).trans
          (Subrepresentation.quotientEquivTopSubquotient A).symm)
    refine ((append (P₁ := fun x : Σ j : Fin m, κ j.castSucc ↦ R x.1.castSucc x.2)
      (P₂ := R (Fin.last m)) A (fun _ ↦ hR _ _) (fun _ ↦ hR _ _) h₁ h₂).reindex
      (sigmaFinSuccEquiv κ)).mono fun x {_} {_} {_} τ hx ↦ ?_
    · obtain ⟨i, y⟩ := x
      induction i using Fin.lastCases with
      | last => simpa [sigmaFinSuccEquiv] using hx
      | cast j => simpa [sigmaFinSuccEquiv] using hx

/-- **Refinement of a filtration.** If `ρ` has a filtration whose graded pieces satisfy `P i`,
and every representation satisfying `P i` has a filtration with graded pieces `R i j`, then these
refine the first filtration: `ρ` has a filtration with graded pieces `R i j` for all `(i, j)`.
(blueprint: `lem-mg-filtration-refinement`) -/
theorem trans (h : HasGradedPieces ρ P) {κ : ι → Type*}
    {R : ∀ i, κ i → RepProp.{u, v} k W} (hR : ∀ i j, RepProp.IsInvariant (R i j))
    (hPR : ∀ i {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y} (τ : Representation k W Y),
      P i τ → HasGradedPieces τ (R i)) :
    HasGradedPieces ρ fun x : Σ i, κ i ↦ R x.1 x.2 := by
  obtain ⟨m, F, e, hF, h0, hl, hPF⟩ := h
  obtain ⟨m', F', e', hF', h0', hl', hRF'⟩ := trans_aux m ρ F hF h0 hl
    (fun i ↦ κ (e i)) (fun i ↦ R (e i)) (fun _ _ ↦ hR _ _) fun i ↦ hPR _ _ (hPF i)
  exact ⟨m', F', e'.trans (Equiv.sigmaCongrLeft e), hF', h0', hl', hRF'⟩
end HasGradedPieces

end Representation

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W] {V : Type v} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- A finite filtration `F` is a filtration with graded pieces its subquotients
`F (i + 1) / F i`. -/
theorem hasGradedPieces_of_monotone {m : ℕ} (F : Fin (m + 1) → Subrepresentation ρ)
    (hF : Monotone F) (h0 : F 0 = ⊥) (hl : F (Fin.last m) = ⊤) :
    HasGradedPieces ρ fun i : Fin m ↦ EquivTo ((F i.succ).subquotient (F i.castSucc)) :=
  ⟨m, F, .refl _, hF, h0, hl, fun _ ↦ ⟨.refl _⟩⟩

namespace CompositionSeries

/-- A composition series is a filtration whose graded pieces are its composition factors. -/
theorem hasGradedPieces (s : ρ.CompositionSeries) :
    HasGradedPieces ρ fun i : Fin s.length ↦ EquivTo (s.factor i) :=
  hasGradedPieces_of_monotone s.series (Fin.monotone_iff_le_succ.2 fun i ↦ (s.covBy i).le)
    s.head_eq s.last_eq

/-- A filtration with irreducible graded pieces is a composition series. -/
theorem exists_of_hasGradedPieces {ι : Type*} {P : ι → RepProp.{u, v} k W}
    (h : HasGradedPieces ρ P)
    (hirr : ∀ i {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y} (τ : Representation k W Y),
      P i τ → τ.IsIrreducible) :
    ∃ (s : ρ.CompositionSeries) (e : Fin s.length ≃ ι), ∀ j, P (e j) (s.factor j) := by
  obtain ⟨m, F, e, hF, h0, hl, hP⟩ := h
  let s : ρ.CompositionSeries :=
    ⟨⟨m, F, fun i ↦ (Subrepresentation.isIrreducible_subquotient_iff
      (hF i.castSucc_le_succ)).1 (hirr _ _ (hP i))⟩, h0, hl⟩
  exact ⟨s, e, hP⟩

/-- **Jordan–Hölder for filtrations with irreducible graded pieces.** If `ρ` has a filtration
whose graded pieces are irreducible and satisfy invariant properties `P i`, then the factors of any
composition series `c` of `ρ` satisfy these properties, along a bijection. -/
theorem exists_equiv_of_hasGradedPieces {ι : Type*} {P : ι → RepProp.{u, v} k W}
    (h : HasGradedPieces ρ P) (hP : ∀ i, RepProp.IsInvariant (P i))
    (hirr : ∀ i {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y} (τ : Representation k W Y),
      P i τ → τ.IsIrreducible) (c : ρ.CompositionSeries) :
    ∃ e : Fin c.length ≃ ι, ∀ j, P (e j) (c.factor j) := by
  obtain ⟨c', e', he'⟩ := exists_of_hasGradedPieces h hirr
  obtain ⟨e, he⟩ := jordanHolder c c'
  exact ⟨e.trans e', fun j ↦ hP _ (he j).some.symm (he' (e j))⟩

/-- **Composition factors of a filtered representation.** Let `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = V` be a
finite filtration, and choose a composition series `t i` of each graded piece `F_{i+1} / F_i`. Then
the composition factors of any composition series `c` of `V` are, up to equivalence and with
multiplicities, the composition factors of all the `t i`: there is a bijection between the factors
of `c` and the pairs `(i, j)` of an index `i` and a factor `j` of `t i`, matching equivalent
factors. (blueprint: `lem-mg-filtration-refinement`) -/
theorem exists_equiv_sigma_of_monotone {m : ℕ} (F : Fin (m + 1) → Subrepresentation ρ)
    (hF : Monotone F) (h0 : F 0 = ⊥) (hl : F (Fin.last m) = ⊤)
    (t : ∀ i : Fin m, ((F i.succ).subquotient (F i.castSucc)).CompositionSeries)
    (c : ρ.CompositionSeries) :
    ∃ e : Fin c.length ≃ Σ i, Fin (t i).length,
      ∀ j, Nonempty ((c.factor j).Equiv ((t (e j).1).factor (e j).2)) := by
  have h := (hasGradedPieces_of_monotone F hF h0 hl).trans
    (R := fun i j ↦ EquivTo ((t i).factor j)) (fun _ _ ↦ isInvariant_equivTo _)
    fun i {_} {_} {_} τ ⟨f⟩ ↦ (t i).hasGradedPieces.of_equiv (fun _ ↦ isInvariant_equivTo _) f.symm
  have hirr : ∀ (x : Σ i, Fin (t i).length) {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y}
      (τ : Representation k W Y), EquivTo ((t x.1).factor x.2) τ → τ.IsIrreducible :=
    fun x {_} {_} {_} τ hτ ↦ hτ.some.isIrreducible_iff.2 ((t x.1).isIrreducible_factor x.2)
  exact exists_equiv_of_hasGradedPieces h (fun _ ↦ isInvariant_equivTo _) hirr c

end CompositionSeries

end Representation
