/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker C1
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Short exact sequences of continuous inhomogeneous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG, section continuous-group-cohomology
(blueprint: lem-exc-continuous-cochains-short-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- Continuous inhomogeneous cochains carry a short exact sequence of discrete continuous
representations to a short exact sequence of complexes. The equivalences `e` identify
complex terms with continuous maps, and specify both differentials and postcomposition maps.
The final term of the sum, indexed by `Fin.last n`, omits the last argument; the other terms
multiply adjacent arguments. At `n = 0` the formula is `g • m - m`.

Proof: (1) Underlying module exactness follows from `lem-exc-discrete-modules-abelian`.
Postcomposition with the injection is injective. A cochain in the kernel has a unique
pointwise preimage, continuous since inverse images of singletons are open. A set-theoretic
section of the surjection is continuous between discrete modules and lifts every cochain.
(2) Projections, adjacent multiplication and the action are continuous; the displayed
alternating sum therefore defines a continuous linear differential. Expanding two successive
differentials cancels all terms in pairs, using associativity and the action law, including
in degree zero. (3) Equivariant linear maps commute with each term of the differential,
so postcomposition gives cochain maps. Degreewise exactness gives short exactness of complexes
by `lem-weil-pbc-cochain-complexes-degreewise-exact`.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential and paragraph
beginning "However, a short exact sequence of discrete G-modules"
(blueprint: lem-exc-continuous-cochains-short-exact). -/
theorem continuousCochains_shortExact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (S : ShortComplex (DiscreteContinuousRep.{v, u, w} A G)) :
    S.ShortExact →
    let X : Fin 3 → DiscreteContinuousRep.{v, u, w} A G := ![S.X₁, S.X₂, S.X₃]
    letI : ∀ j : Fin 3, TopologicalSpace (X j).obj.V := fun _ ↦ ⊥
    letI : ∀ j : Fin 3, DiscreteTopology (X j).obj.V := fun _ ↦ ⟨rfl⟩
    letI : ∀ j : Fin 3, ContinuousConstSMul A (X j).obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    ∃ (K : Fin 3 → CochainComplex (ModuleCat.{max u w} A) ℕ)
      (e : ∀ (j : Fin 3) (n : ℕ),
        (K j).X n ≃ₗ[A] C((Fin n → G), (X j).obj.V))
      (i : K 0 ⟶ K 1) (p : K 1 ⟶ K 2) (hip : i ≫ p = 0),
      (ShortComplex.mk i p hip).ShortExact ∧
      (∀ n : ℕ, Function.Injective (i.f n) ∧
        Set.range (i.f n) = {x | p.f n x = 0} ∧ Function.Surjective (p.f n)) ∧
      (∀ (n : ℕ) (f : (K 0).X n) (g : Fin n → G),
        e 1 n (i.f n f) g = S.f.hom.hom (e 0 n f g)) ∧
      (∀ (n : ℕ) (f : (K 1).X n) (g : Fin n → G),
        e 2 n (p.f n f) g = S.g.hom.hom (e 1 n f g)) ∧
      (∀ (j : Fin 3) (n : ℕ) (f : (K j).X n) (g : Fin (n + 1) → G),
        e j (n + 1) ((K j).d n (n + 1) f) g =
          (X j).obj.ρ (g 0) (e j n f (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • e j n f (Fin.contractNth k (· * ·) g)) := by
  sorry

end Rep
