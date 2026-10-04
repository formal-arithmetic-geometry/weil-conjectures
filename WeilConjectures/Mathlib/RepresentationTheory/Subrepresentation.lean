/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Subquotients of a representation, and translates of subrepresentations

`Mathlib.RepresentationTheory.Subrepresentation` provides the lattice `Subrepresentation ρ` of
subrepresentations of `ρ : Representation k W V` and, for a single subrepresentation `S`, the
representation `S.toRepresentation` on `S`.  This file adds the subquotient: for
subrepresentations `U ≤ S` the representation of `W` on `S ⧸ U`.

It also adds two order isomorphisms of lattices of subrepresentations: the translation
`U ↦ ρ g U` of subrepresentations of the restriction of `ρ` to a normal subgroup, and the
identification of the lattices of two representations on the same space with the same invariant
subspaces.

`U` is presented inside `S` as `U.toSubmodule.comap S.toSubmodule.subtype`, so that no inclusion
`U ≤ S` is needed to *form* the quotient; the interesting case is of course `U ≤ S`, where the
quotient is the honest subquotient `S / U`.

## Main declarations

* `Subrepresentation.subquotient`: the representation of `W` on `S ⧸ U`.
* `Subrepresentation.translate`: translation by `g` of subrepresentations of the restriction to a
  normal subgroup.
* `Subrepresentation.orderIsoOfForallIff`: representations with the same invariant subspaces have
  the same lattice of subrepresentations.
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

end Subrepresentation

namespace Subrepresentation

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

section Translate

variable (ρ : Representation k G V) (N : Subgroup G) [N.Normal]

/-- For a normal subgroup `N` of `G`, the translate `ρ g U` of a subrepresentation `U` of the
restriction of `ρ` to `N` is again a subrepresentation: `n (g u) = g ((g⁻¹ n g) u)`. -/
def translateFun (g : G) (U : Subrepresentation (ρ.comp N.subtype)) :
    Subrepresentation (ρ.comp N.subtype) where
  toSubmodule := U.toSubmodule.map (ρ g)
  apply_mem_toSubmodule n := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨ρ (g⁻¹ * n * g) u, U.apply_mem_toSubmodule ⟨g⁻¹ * n * g, ?_⟩ hu, ?_⟩
    · simpa using ‹N.Normal›.conj_mem _ n.2 g⁻¹
    · simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]

variable {ρ N} in
theorem mem_translateFun {g : G} {U : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ translateFun ρ N g U ↔ ρ g⁻¹ v ∈ U := by
  change v ∈ U.toSubmodule.map (ρ g) ↔ _
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro hv
    refine ⟨_, hv, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Translation `U ↦ ρ g U` by an element `g ∈ G` is an order automorphism of the lattice of
subrepresentations of the restriction of `ρ` to a normal subgroup `N`. -/
def translate (g : G) :
    Subrepresentation (ρ.comp N.subtype) ≃o Subrepresentation (ρ.comp N.subtype) where
  toFun := translateFun ρ N g
  invFun := translateFun ρ N g⁻¹
  left_inv U := SetLike.ext fun v ↦ by
    simp only [mem_translateFun, inv_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  right_inv U := SetLike.ext fun v ↦ by
    simp only [mem_translateFun, inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]
  map_rel_iff' {U U'} := by
    change translateFun ρ N g U ≤ translateFun ρ N g U' ↔ U ≤ U'
    refine ⟨fun h v hv ↦ ?_, fun h v hv ↦ mem_translateFun.2 (h (mem_translateFun.1 hv))⟩
    have := @h (ρ g v) (by
      rwa [mem_translateFun, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply])
    rwa [mem_translateFun, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this

variable {ρ N} in
theorem mem_translate {g : G} {U : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ translate ρ N g U ↔ ρ g⁻¹ v ∈ U :=
  mem_translateFun

end Translate

section OrderIsoOfForallIff

variable {H : Type*} [Monoid H] {ρ : Representation k G V} {σ : Representation k H V}

/-- Two representations on the same module with the same invariant submodules have the same
subrepresentations. -/
def orderIsoOfForallIff
    (h : ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) ↔ ∀ g, ∀ v ∈ U, σ g v ∈ U) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule, fun g _ hv ↦ (h U.toSubmodule).1
    (fun g _ hv ↦ U.apply_mem_toSubmodule g hv) g _ hv⟩
  invFun U := ⟨U.toSubmodule, fun g _ hv ↦ (h U.toSubmodule).2
    (fun g _ hv ↦ U.apply_mem_toSubmodule g hv) g _ hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end OrderIsoOfForallIff

end Subrepresentation
