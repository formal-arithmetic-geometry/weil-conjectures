/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Mathlib.Topology.Separation.Profinite
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Abelian structure on discrete modules with a continuous group action

Source: Stacks Project, Etale Cohomology, Definition 04JP and the following paragraph,
in Section 0A2H (blueprint: lem-exc-discrete-modules-abelian-structure).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Stacks Project, Definition 04JP and the paragraph after it (Section 0A2H).
The zero module has its unique action. Binary direct sums have componentwise action and
open stabilizers by intersection. An equivariant map has the ordinary module kernel,
whose stabilizers stay open, and the ordinary quotient cokernel, whose stabilizers contain
the open stabilizers of representatives. The usual universal properties are equivariant.
Addition of maps is equivariant; mono and epi coincide with injective and surjective maps,
respectively. These calculations give the abelian-category criterion of `def-sp-abelian`.
The image and kernel computed in this category are the underlying module image and kernel,
so exactness at each term is exactly underlying module exactness.
(blueprint: lem-exc-discrete-modules-abelian-structure) -/
theorem discreteRep_abelian_structure (A : Type u) [Ring A] [Finite A]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ h : CategoryTheory.Abelian (DiscreteContinuousRep.{u, v, w} A G),
      (letI : CategoryTheory.Abelian (DiscreteContinuousRep.{u, v, w} A G) := h
       let forgetDiscrete : DiscreteContinuousRep.{u, v, w} A G ⥤ ModuleCat.{w} A :=
         (ObjectProperty.ι (fun X : Rep.{w} A G =>
           ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})) ⋙
           forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
       forgetDiscrete.Additive ∧
       PreservesFiniteLimits forgetDiscrete ∧
       PreservesFiniteColimits forgetDiscrete ∧
       ∀ S : ShortComplex (DiscreteContinuousRep.{u, v, w} A G),
         S.Exact ↔ (S.map forgetDiscrete).Exact) := by
  sorry

end Rep
