/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E2
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Sheaf.CategoryTheory.DeltaFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.ContinuousCochainsShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Continuous cochain delta-functor

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-delta-functor).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Continuous inhomogeneous cochains form a cohomological delta-functor.

Proof: Construct each term as the module of continuous maps to the discrete coefficient
module. The action, projections and adjacent multiplication preserve continuity, and
expanding two differentials cancels the terms in pairs. Postcomposition by equivariant
linear maps commutes with the differential and gives a functor. The short exactness theorem
`lem-exc-continuous-cochains-short-exact` applies to these complexes: transport its maps
along their term equivalences. The homology long exact sequence and its naturality give
all the delta-functor axioms, including additivity and the initial monomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology; final profinite comparison via coinduction.
(blueprint: lem-exc-continuous-cochains-delta-functor). -/
theorem continuousCochains_deltaFunctor
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
        ∃ T : CohomologicalDeltaFunctor
            (DiscreteContinuousRep.{v, u, max u w} A G) (ModuleCat.{max u w} A),
          T.F = (fun q ↦ F ⋙ HomologicalComplex.homologyFunctor
            (ModuleCat.{max u w} A) (ComplexShape.up ℕ) q) := by
  sorry

end Rep
