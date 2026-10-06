/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.Mathlib.RepresentationTheory.Basic

/-!
# Subquotients of a representation

`Mathlib.RepresentationTheory.Subrepresentation` provides the lattice `Subrepresentation ρ` of
subrepresentations of `ρ : Representation k W V` and, for a single subrepresentation `S`, the
representation `S.toRepresentation` on `S`.  This file adds the subquotient: for
subrepresentations `U ≤ S` the representation of `W` on `S ⧸ U`.

`U` is presented inside `S` as `U.toSubmodule.comap S.toSubmodule.subtype`, so that no inclusion
`U ≤ S` is needed to *form* the quotient; the interesting case is of course `U ≤ S`, where the
quotient is the honest subquotient `S / U`.

## Main declarations

* `Subrepresentation.subquotient`: the representation of `W` on `S ⧸ U`.
* `Subrepresentation.orderIsoMapComap`: subrepresentations correspond along an equivalence of
  representations, and so do the determinant characters of their subquotients
  (`Subrepresentation.detCharacter_subquotient_orderIsoMapComap`).
* `Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible`: Schur's lemma on an irreducible
  subquotient, over an algebraically closed field.
-/

@[expose] public section

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}

/-- The representation induced on the subquotient `S ⧸ U` of two subrepresentations of `ρ`. -/
noncomputable def subquotient (S U : Subrepresentation ρ) :
    Representation k W (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) where
  toFun w := Submodule.mapQ _ _ ((ρ w).restrict (S.apply_mem_toSubmodule w)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    simpa only [LinearMap.coe_restrict_apply] using U.apply_mem_toSubmodule w hx)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_one]
    exact congrArg _ (Subtype.ext (by simp))
  map_mul' v w := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul]
    exact congrArg _ (Subtype.ext (by simp))

@[simp]
theorem subquotient_apply_mk (S U : Subrepresentation ρ) (w : W) (x : S.toSubmodule) :
    S.subquotient U w (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨ρ w x, S.apply_mem_toSubmodule w x.2⟩ :=
  rfl

theorem toSubmodule_le_toSubmodule {S T : Subrepresentation ρ} :
    S.toSubmodule ≤ T.toSubmodule ↔ S ≤ T :=
  Iff.rfl

section Equiv

variable {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k W V'}

/-- Subrepresentations correspond along an equivalence of representations `e`: `S ↦ e(S)`. -/
def orderIsoMapComap (e : ρ.Equiv σ) : Subrepresentation ρ ≃o Subrepresentation σ where
  toFun S := ⟨S.toSubmodule.map (e.toLinearEquiv : V →ₗ[k] V'), by
    rintro w _ ⟨x, hx, rfl⟩
    exact ⟨ρ w x, S.apply_mem_toSubmodule w hx, e.apply_apply w x⟩⟩
  invFun S := ⟨S.toSubmodule.comap (e.toLinearEquiv : V →ₗ[k] V'), by
    intro w x hx
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, e.toLinearEquiv_apply, e.coe_toIntertwiningMap,
      e.apply_apply]
    exact S.apply_mem_toSubmodule w hx⟩
  left_inv S := toSubmodule_injective
    (Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective _)
  right_inv S := toSubmodule_injective
    (Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective _)
  map_rel_iff' {S T} := by
    rw [← toSubmodule_le_toSubmodule, ← toSubmodule_le_toSubmodule]
    exact Submodule.map_le_map_iff_of_injective e.toLinearEquiv.injective _ _

theorem mem_orderIsoMapComap_iff (e : ρ.Equiv σ) (S : Subrepresentation ρ) {y : V'} :
    y ∈ orderIsoMapComap e S ↔ e.symm y ∈ S :=
  Submodule.mem_map_equiv (p := S.toSubmodule) (e := e.toLinearEquiv)

theorem apply_mem_orderIsoMapComap (e : ρ.Equiv σ) (S : Subrepresentation ρ) {x : V}
    (hx : x ∈ S) : e x ∈ orderIsoMapComap e S :=
  ⟨x, hx, rfl⟩

/-- The equivalence between the subquotients `S ⧸ U` and `e(S) ⧸ e(U)` induced by an equivalence
of representations `e`. -/
noncomputable def subquotientEquiv (e : ρ.Equiv σ) (S U : Subrepresentation ρ) :
    (S.subquotient U).Equiv ((orderIsoMapComap e S).subquotient (orderIsoMapComap e U)) :=
  .mk (Submodule.Quotient.equiv _ _ (e.toLinearEquiv.submoduleMap S.toSubmodule) <| by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply]
    exact (mem_orderIsoMapComap_iff e U).symm) fun w ↦ by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
      subquotient_apply_mk, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (e.apply_apply w x)

/-- The subquotients `S ⧸ U` and `e(S) ⧸ e(U)` along an equivalence of representations `e` have the
same determinant character. -/
theorem detCharacter_subquotient_orderIsoMapComap (e : ρ.Equiv σ) (S U : Subrepresentation ρ) :
    ((orderIsoMapComap e S).subquotient (orderIsoMapComap e U)).detCharacter =
      (S.subquotient U).detCharacter :=
  (subquotientEquiv e S U).detCharacter_eq

end Equiv

/-- The subquotient `S ⧸ ⊥` is equivalent to `S`. -/
noncomputable def subquotientBotEquiv (S : Subrepresentation ρ) :
    (S.subquotient ⊥).Equiv S.toRepresentation :=
  .mk (Submodule.quotEquivOfEqBot _ <| by
    ext x
    exact ⟨fun h ↦ (Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 h)),
      fun h ↦ by rw [(Submodule.mem_bot k).1 h]; exact zero_mem _⟩) fun w ↦
    Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl)

theorem detCharacter_subquotient_bot (S : Subrepresentation ρ) :
    (S.subquotient ⊥).detCharacter = S.toRepresentation.detCharacter :=
  (subquotientBotEquiv S).detCharacter_eq.symm

/-- **Schur's lemma** on a subquotient: over an algebraically closed field, an endomorphism that
commutes with the action and preserves `U` and `S` acts on an irreducible subquotient `S ⧸ U` by a
scalar. -/
theorem exists_apply_sub_smul_mem_of_isIrreducible [IsAlgClosed k] [FiniteDimensional k V]
    {U S : Subrepresentation ρ} (hirr : (S.subquotient U).IsIrreducible) (f : V →ₗ[k] V)
    (hf : ∀ w x, f (ρ w x) = ρ w (f x)) (hU : ∀ x ∈ U, f x ∈ U) (hS : ∀ x ∈ S, f x ∈ S) :
    ∃ c : k, ∀ x ∈ S, f x - c • x ∈ U := by
  let fQ : Representation.IntertwiningMap (S.subquotient U) (S.subquotient U) :=
    { toLinearMap := Submodule.mapQ _ _ (f.restrict hS) fun x hx ↦ hU _ hx
      isIntertwining' w := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
          subquotient_apply_mk]
        congr 1
        exact Subtype.ext (hf w x) }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := S.subquotient U)).2 fQ
  refine ⟨c, fun x hx ↦ ?_⟩
  have h : c • (Submodule.Quotient.mk ⟨x, hx⟩ :
      S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk ⟨f x, hS x hx⟩ :=
    congrArg (fun g : Representation.IntertwiningMap (S.subquotient U) (S.subquotient U) ↦
      g (Submodule.Quotient.mk ⟨x, hx⟩)) hc
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at h
  exact h

end Subrepresentation
