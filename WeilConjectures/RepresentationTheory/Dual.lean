/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.RepresentationTheory.Filtration

/-!
# Filtrations of the contragredient representation

Let `ρ` be a representation of a group `W` on a `k`-vector space `V`, and `ρ^∨ = ρ.dual` its
contragredient on `V^∨ = Hom_k(V, k)`. A subrepresentation `U ≤ V` has an *annihilator*
`U^⊥ ≤ V^∨`, again a subrepresentation, and `U ↦ U^⊥` reverses inclusions. For `U ≤ S` the
subquotient `U^⊥ / S^⊥` of `ρ^∨` is the contragredient of the subquotient `S / U`: a linear form
on `S / U` is a linear form on `S` vanishing on `U`, and extends to `V` because `k` is a field.

Consequently a finite filtration `0 = F₀ ≤ ⋯ ≤ F_m = V` induces the filtration
`0 = F_m^⊥ ≤ ⋯ ≤ F₀^⊥ = V^∨` of `ρ^∨`, whose graded pieces are the contragredients of the graded
pieces of `F`, and the constituents of `ρ^∨` are the contragredients of those of `ρ`. This is the
case of the dual in part L3 (tensor filtration) of the linear-algebra library `sk-r-linear-library`;
the cases of tensor products and exterior powers are `Representation.HasGradedPieces.tprod_left`,
`Representation.CompositionSeries.hasGradedPieces_tprod` and
`Representation.CompositionSeries.hasGradedPieces_exteriorPower`.

## Main definitions

- `Subrepresentation.dualAnnihilator`: the annihilator `U^⊥` of a subrepresentation, a
  subrepresentation of the contragredient.
- `Subrepresentation.subquotientDualEquiv`: the equivalence `U^⊥ / S^⊥ ≅ (S / U)^∨`.

## Main results

- `Representation.IsIrreducible.dual`: the contragredient of a finite-dimensional irreducible
  representation is irreducible.
- `Representation.HasGradedPieces.dual`: the dual filtration of the contragredient has as graded
  pieces the contragredients of the graded pieces.
- `Representation.CompositionSeries.exists_equiv_dual`: the composition factors of `ρ^∨` are the
  contragredients of the composition factors of `ρ`, with multiplicities.
- `Representation.ConstituentsLE.dual`: if every constituent of `ρ` is a constituent of `σ`, then
  every constituent of `ρ^∨` is a constituent of `σ^∨`.
-/

@[expose] public section

open Module

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V V' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k W V} {σ : Representation k W V'}

/-- Equivalent representations have equivalent contragredients. -/
noncomputable def Equiv.dualCongr (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  .mk e.toLinearEquiv.symm.dualMap fun w ↦ by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply, dual_apply, Dual.transpose_apply,
      LinearMap.comp_apply]
    congr 1
    exact (e.symm.apply_apply w⁻¹ x).symm

end Representation

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The *annihilator* `U^⊥` of a subrepresentation `U`: the linear forms vanishing on `U`, a
subrepresentation of the contragredient representation. -/
def dualAnnihilator (U : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := U.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule w f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro x hx
    rw [Representation.dual_apply, Dual.transpose_apply, LinearMap.comp_apply]
    exact hf _ (U.apply_mem_toSubmodule w⁻¹ hx)

theorem mem_dualAnnihilator {U : Subrepresentation ρ} {f : Dual k V} :
    f ∈ U.dualAnnihilator ↔ ∀ x ∈ U, f x = 0 :=
  Submodule.mem_dualAnnihilator f

theorem dualAnnihilator_antitone : Antitone (dualAnnihilator : Subrepresentation ρ → _) :=
  fun _ _ h ↦ Submodule.dualAnnihilator_anti (toSubmodule_le_toSubmodule.2 h)

@[simp]
theorem dualAnnihilator_bot : (⊥ : Subrepresentation ρ).dualAnnihilator = ⊤ :=
  toSubmodule_injective Submodule.dualAnnihilator_bot

@[simp]
theorem dualAnnihilator_top : (⊤ : Subrepresentation ρ).dualAnnihilator = ⊥ :=
  toSubmodule_injective Submodule.dualAnnihilator_top

/-- For `U ≤ S`, a linear form on `V` vanishing on `U` induces a linear form on the subquotient
`S / U`. -/
noncomputable def dualAnnihilatorToDualSubquotient (U S : Subrepresentation ρ) :
    U.dualAnnihilator.toSubmodule →ₗ[k]
      Dual k (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) where
  toFun f := Submodule.liftQ _ ((f : Dual k V) ∘ₗ S.toSubmodule.subtype) fun x hx ↦
    mem_dualAnnihilator.1 f.2 x hx
  map_add' _ _ := Submodule.linearMap_qext _ rfl
  map_smul' _ _ := Submodule.linearMap_qext _ rfl

@[simp]
theorem dualAnnihilatorToDualSubquotient_apply_mk (U S : Subrepresentation ρ)
    (f : U.dualAnnihilator.toSubmodule) (x : S.toSubmodule) :
    dualAnnihilatorToDualSubquotient U S f (Submodule.Quotient.mk x) = (f : Dual k V) x :=
  rfl

theorem ker_dualAnnihilatorToDualSubquotient (U S : Subrepresentation ρ) :
    LinearMap.ker (dualAnnihilatorToDualSubquotient U S) =
      S.dualAnnihilator.toSubmodule.comap U.dualAnnihilator.toSubmodule.subtype := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨fun h ↦ mem_dualAnnihilator.2 fun x hx ↦ ?_, fun h ↦ Submodule.linearMap_qext _ ?_⟩
  · simpa using congr($h (Submodule.Quotient.mk ⟨x, hx⟩))
  · exact LinearMap.ext fun x ↦ mem_dualAnnihilator.1 h x x.2

theorem dualAnnihilatorToDualSubquotient_surjective {U S : Subrepresentation ρ} (h : U ≤ S) :
    Function.Surjective (dualAnnihilatorToDualSubquotient U S) := by
  intro φ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (φ ∘ₗ Submodule.mkQ _ : S.toSubmodule →ₗ[k] k)
  have hgU : g ∈ U.dualAnnihilator := mem_dualAnnihilator.2 fun x hx ↦ by
    have := congr($hg ⟨x, h hx⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact (congrArg φ ((Submodule.Quotient.mk_eq_zero _).2 hx)).trans (map_zero φ)
  exact ⟨⟨g, hgU⟩, Submodule.linearMap_qext _ hg⟩

/-- **The contragredient of a subquotient.** For subrepresentations `U ≤ S`, the subquotient
`U^⊥ / S^⊥` of the contragredient representation is the contragredient of the subquotient `S / U`.
(blueprint: part L3 of `sk-r-linear-library`) -/
noncomputable def subquotientDualEquiv {U S : Subrepresentation ρ} (h : U ≤ S) :
    (U.dualAnnihilator.subquotient S.dualAnnihilator).Equiv (S.subquotient U).dual :=
  .mk ((Submodule.quotEquivOfEq _ _ (ker_dualAnnihilatorToDualSubquotient U S).symm).trans
    ((dualAnnihilatorToDualSubquotient U S).quotKerEquivOfSurjective
      (dualAnnihilatorToDualSubquotient_surjective h))) fun w ↦ by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun f ↦ Submodule.linearMap_qext _
      (LinearMap.ext fun x ↦ ?_))
    rfl

end Subrepresentation

namespace Representation

section Irreducible

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The contragredient of a finite-dimensional irreducible representation is irreducible: the
annihilator in `V` of an invariant subspace of `V^∨` is invariant, hence `0` or `V`.
(blueprint: part L3 of `sk-r-linear-library`) -/
theorem IsIrreducible.dual [FiniteDimensional k V] (h : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  obtain ⟨hV, hU⟩ := isIrreducible_iff.1 h
  refine isIrreducible_iff.2 ⟨(Module.nontrivial_dual_iff k).2 hV, fun T hT ↦ ?_⟩
  have hC : ∀ g, ∀ v ∈ T.dualCoannihilator, ρ g v ∈ T.dualCoannihilator := fun g v hv ↦ by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have := hv _ (hT g⁻¹ f hf)
    simp only [dual_apply, inv_inv] at this
    exact this
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := T)]
  rcases hU _ hC with h | h <;> rw [h]
  · exact Or.inr Submodule.dualAnnihilator_bot
  · exact Or.inl Submodule.dualAnnihilator_top

end Irreducible

namespace HasGradedPieces

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V} {ι : Type*} {X : ι → Type*} [∀ i, AddCommGroup (X i)]
  [∀ i, Module k (X i)] {τ : ∀ i, Representation k W (X i)}

/-- **The dual filtration.** If `ρ` has a finite filtration with graded pieces equivalent to the
`τ i`, then the annihilators of the filtration form a finite filtration of the contragredient
`ρ^∨` whose graded pieces are equivalent to the contragredients `τ i ^∨`.
(blueprint: part L3 of `sk-r-linear-library`) -/
theorem dual (h : HasGradedPieces ρ fun i ↦ EquivTo (τ i)) :
    HasGradedPieces ρ.dual fun i ↦ EquivTo (τ i).dual := by
  obtain ⟨m, F, e, hF, h0, hl, hP⟩ := h
  refine ⟨m, fun j ↦ (F j.rev).dualAnnihilator, Fin.revPerm.trans e,
    fun i j hij ↦ Subrepresentation.dualAnnihilator_antitone (hF (Fin.rev_le_rev.2 hij)),
    by simp [hl], by simp [h0], fun i ↦ ?_⟩
  exact ⟨(Subrepresentation.subquotientCongr (congrArg _ (congrArg F (Fin.rev_succ i)))
    (congrArg _ (congrArg F (Fin.rev_castSucc i)))).trans
    ((Subrepresentation.subquotientDualEquiv (hF i.rev.castSucc_le_succ)).trans
      (hP i.rev).equiv.dualCongr)⟩

end HasGradedPieces

namespace CompositionSeries

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The annihilators of a composition series of `ρ` form a filtration of the contragredient whose
graded pieces are the contragredients of the composition factors.
(blueprint: part L3 of `sk-r-linear-library`) -/
theorem hasGradedPieces_dual (s : ρ.CompositionSeries) :
    HasGradedPieces ρ.dual fun i : Fin s.length ↦ EquivTo (s.factor i).dual :=
  s.hasGradedPieces.dual

/-- **Composition factors of the contragredient.** For a finite-dimensional representation `ρ`,
the composition factors of any composition series `c` of the contragredient `ρ^∨` are, with
multiplicities, the contragredients of the composition factors of a composition series `s` of `ρ`.
(blueprint: part L3 of `sk-r-linear-library`) -/
theorem exists_equiv_dual [FiniteDimensional k V] (s : ρ.CompositionSeries)
    (c : ρ.dual.CompositionSeries) :
    ∃ e : Fin c.length ≃ Fin s.length, ∀ j, Nonempty ((c.factor j).Equiv (s.factor (e j)).dual) :=
  exists_equiv_of_hasGradedPieces s.hasGradedPieces_dual (fun _ ↦ isInvariant_equivTo _)
    (fun i {_} {_} {_} _ hτ ↦ hτ.some.isIrreducible_iff.2 (s.isIrreducible_factor i).dual) c

end CompositionSeries

namespace ConstituentsLE

variable {k : Type*} [Field k] {W : Type*} [Group W] {V V' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k W V} {σ : Representation k W V'}

/-- The constituents of a subquotient of `σ` are constituents of `σ`. -/
theorem subquotient (S U : Subrepresentation σ) : ConstituentsLE (S.subquotient U) σ :=
  ((of_equiv (Subrepresentation.quotientComapSubtypeEquiv U S).symm).trans
    (of_surjective _ (Subrepresentation.mkQ_surjective _))).trans
    (of_injective S.subtype S.subtype_injective)

/-- **Constituents of contragredients.** If every constituent of the finite-dimensional
representation `ρ` is a constituent of `σ`, then every constituent of the contragredient `ρ^∨` is
a constituent of `σ^∨`. (blueprint: part L3 of `sk-r-linear-library`) -/
theorem dual [FiniteDimensional k V] (h : ConstituentsLE ρ σ) : ConstituentsLE ρ.dual σ.dual := by
  obtain ⟨s⟩ := ρ.exists_compositionSeries
  -- the contragredient of a composition factor `S' / U'` of `σ` is the subquotient
  -- `(U' ⊓ S')^⊥ / S'^⊥` of `σ^∨`
  have hfac (i : Fin s.length) : ConstituentsLE (s.factor i).dual σ.dual := by
    obtain ⟨U', S', -, ⟨e⟩⟩ := h _ _ (s.isIrreducible_factor i)
    exact ((of_equiv (e.trans (Subrepresentation.subquotientInfEquiv U' S').symm).dualCongr).trans
      (of_equiv (Subrepresentation.subquotientDualEquiv inf_le_right).symm)).trans
      (subquotient _ _)
  -- the annihilators of the composition series form a decreasing filtration of `ρ^∨`
  have hmono : Monotone s.series := Fin.monotone_iff_le_succ.2 fun i ↦ (s.covBy i).le
  let F : ℕ → Subrepresentation ρ.dual := fun j ↦
    (s.series ⟨min j s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩).dualAnnihilator
  refine of_chain F (fun j ↦ Subrepresentation.dualAnnihilator_antitone
    (hmono (Fin.mk_le_mk.2 (by omega)))) ?_ (m := s.length) ?_ fun j hj ↦ ?_
  · change (s.series ⟨min 0 s.length, _⟩).dualAnnihilator = ⊤
    rw [show (⟨min 0 s.length, _⟩ : Fin (s.length + 1)) = 0 from Fin.ext (by simp),
      show s.series 0 = ⊥ from s.head_eq, Subrepresentation.dualAnnihilator_bot]
  · change (s.series ⟨min s.length s.length, _⟩).dualAnnihilator = ⊥
    rw [show (⟨min s.length s.length, _⟩ : Fin (s.length + 1)) = Fin.last _ from
      Fin.ext (by simp), show s.series (Fin.last _) = ⊤ from s.last_eq,
      Subrepresentation.dualAnnihilator_top]
  · let i : Fin s.length := ⟨j, hj⟩
    refine (of_equiv ((Subrepresentation.subquotientCongr
      (S' := (s.series i.castSucc).dualAnnihilator) (U' := (s.series i.succ).dualAnnihilator)
      (congrArg _ (congrArg s.series (Fin.ext (by simp [i]; omega))))
      (congrArg _ (congrArg s.series (Fin.ext (by simp [i]; omega))))).trans
      (Subrepresentation.subquotientDualEquiv (s.covBy i).le))).trans (hfac i)

end ConstituentsLE

end Representation
