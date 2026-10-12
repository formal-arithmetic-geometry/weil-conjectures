/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker M1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Sheaf.RepresentationTheory.DiscreteContinuousInjectives
import Sheaf.RepresentationTheory.DiscreteRep

/-!
# Discrete modules with profinite group action

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

/-- Enough injectives, module kernels and cokernels, and module-detected exactness for
the discrete-action category once its abelian structure is fixed.

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian). -/
abbrev discreteModuleActionProperties (A : Type v) [Ring A] (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : Abelian (Rep.DiscreteContinuousRep.{v, u, w} A G)) : Prop :=
  letI := h
  let F := ObjectProperty.ι (fun X : Rep.{w} A G =>
    ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
  ∃ (h0 : F.PreservesZeroMorphisms),
    letI := h0
    EnoughInjectives (Rep.DiscreteContinuousRep.{v, u, w} A G) ∧
    PreservesFiniteLimits F ∧
    PreservesFiniteColimits F ∧
    ∀ S : ShortComplex (Rep.DiscreteContinuousRep.{v, u, w} A G),
      S.Exact ↔ (S.map F).Exact

/-- For a morphism, its module kernel is action-stable and its elements retain the open
stabilizers they had in the source. The module cokernel inherits the action and each
class has an open stabilizer containing that of a representative. Thus the zero object,
finite biproducts, kernels and cokernels come from modules; exactness is detected there.
Normality of monos and epis then gives the abelian structure
(`lem-exc-discrete-modules-abelian-structure`, `def-sp-abelian`). By the functorial
injective embedding theorem for discrete actions
(`lem-exc-discrete-modules-abelian-injective-embeddings`), every object embeds into
an injective, giving enough injectives (`def-sp-injective-resolutions`).

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian). -/
theorem discreteModules_abelian
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ (h : Abelian (Rep.DiscreteContinuousRep.{v, u, w} A G)),
      discreteModuleActionProperties.{u, v, w} A G h := by
  sorry

end CategoryTheory
