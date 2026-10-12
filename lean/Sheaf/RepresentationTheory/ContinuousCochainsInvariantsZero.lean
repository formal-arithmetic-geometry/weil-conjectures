/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E2
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Degree-zero cochains and invariants

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-invariants-zero).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Degree-zero continuous cochain homology is the left exact invariant functor.

Proof: A continuous map from the singleton `Fin 0 → G` is a constant coefficient.
The degree-zero differential is the function `g ↦ ρ(g)m - m`, so its kernel is exactly
`⨅ g, ker (ρ(g) - id)`. There are no incoming boundaries in degree zero; the homology
kernel description therefore gives a linear equivalence to this invariant submodule.
Postcomposition commutes with evaluation and with the kernel inclusion, making the
identifications natural. Define the invariant functor on maps by restriction of the
underlying equivariant linear map. Restriction preserves identities, compositions and
addition. This construction is data, independent of any existence choice. Finally the
forgetful functor detects module kernels and finite products by
`lem-exc-discrete-modules-abelian`; taking invariant elements commutes with both kernels
and finite products. Thus the constructed invariant functor preserves finite limits.
The degree-zero equivalences assemble into the asserted natural isomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology, degree-zero differential and invariants.
(blueprint: lem-exc-continuous-cochains-invariants-zero). -/
theorem continuousCochains_invariants_zero
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
    letI : Preadditive (ModuleCat.{max u w} A) :=
      (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
    letI := (Classical.choose_spec
      (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
      fun _ ↦ ⊥
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
      fun _ ↦ ⟨rfl⟩
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        ContinuousConstSMul A M.obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    let S := fun M : DiscreteContinuousRep.{v, u, max u w} A G =>
      ⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id)
    ∀ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        CochainComplex (ModuleCat.{max u w} A) ℕ,
      ∀ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
        (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
          (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
          e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) →
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
          (x : (F.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
            M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) →
    ∃ V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A,
      ∃ a : V.Additive,
        letI instAdditive : V.Additive := a
        ∃ t : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
            V.obj M ≃ₗ[A] S M,
          (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
            (x : V.obj M),
            (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) ∧
          PreservesFiniteLimits V ∧
          Nonempty ((F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
            (ComplexShape.up ℕ) 0) ≅ V) := by
  sorry

end Rep
