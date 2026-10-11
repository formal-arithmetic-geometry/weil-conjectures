/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker C1
-/
import Sheaf.CategoryTheory.DiscreteModulesAbelian
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Continuous inhomogeneous cochains compute derived invariants

Source: Stacks Project, Etale Cohomology, Section 59.58, Tag 0DVG
(blueprint: lem-exc-cochains-derived-invariants).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Continuous inhomogeneous cochains compute the right derived functors of invariants.
The existential complex is specified by linear equivalences of its terms with continuous
maps from `G^n` to the discrete module, its maps on coefficients, and its inhomogeneous
differential; thus it is the usual complex up to natural termwise linear equivalence.
The term of the sum indexed by `Fin.last n` omits the last argument; the other terms
multiply adjacent arguments. In degree zero the formula is `g • m - m`.

Proof, following the DAG: degreewise exactness
(`lem-exc-continuous-cochains-short-exact`), the long exact homology sequence
(`lem-weil-pbc-complex-ses-homology-long-exact`) and its naturality
(`lem-weil-pbc-complex-ses-long-exact-naturality`) give a cohomological delta-functor
(`def-weil-pbc-delta-functor`). Its zeroth term is invariants; invariants are additive
and left exact by `lem-exc-discrete-modules-abelian`. The embedding into continuous
coinduction (`lem-exc-coinduced-discrete-embedding`) and its positive-degree acyclicity
(`lem-exc-coinduced-continuous-acyclic`) efface every positive-degree cochain cohomology.
Apply `lem-weil-pbc-effaceable-delta-functor-universal`. Enough injectives and
`lem-weil-pbc-right-derived-universal-delta-functor` give universality of derived
invariants. The two universal delta-functors extend the identity in degree zero in
both directions; uniqueness makes their composites identities, giving natural
isomorphisms in every degree.

Source: Stacks Project, Etale Cohomology, Section 59.58, Tag 0DVG, displayed
inhomogeneous differential and final profinite comparison
(blueprint: lem-exc-cochains-derived-invariants). -/
theorem continuousCochains_derived_invariants
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
    ∃ V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A,
      ∃ a : V.Additive,
        letI instAdditive : V.Additive := a
        ∃ t : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
            V.obj M ≃ₗ[A] S M,
          (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
            (x : V.obj M),
            (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) ∧
          ∃ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
              CochainComplex (ModuleCat.{max u w} A) ℕ,
            ∃ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
              (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
              (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
                (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
                e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) ∧
              (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
                (x : (F.obj M).X n) (g : Fin (n + 1) → G),
                e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
                  M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
                    ∑ k : Fin (n + 1),
                      (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) ∧
              ∀ q : ℕ, Nonempty ((@Functor.rightDerived _ _ _ _ h _ _ V a q) ≅
                F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
                  (ComplexShape.up ℕ) q) := by
  sorry

end Rep
