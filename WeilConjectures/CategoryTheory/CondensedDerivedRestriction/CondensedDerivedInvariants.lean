/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedBar.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

/-! # Derived restriction calculus for internal condensed actions

Source: main-20261015 direct-images proof, paragraph (3), formal derived-restriction
infrastructure (blueprint: def-sfb-condensed-derived-invariants).
The source records this auxiliary infrastructure as agent-formulated, with a reference wanted.
No assertion that underived continuous cochains compute derived invariants is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The action-site presentation transports the generator, colimits and AB5.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the action-site module equivalence preserves all limits and colimits; apply the
Grothendieck abelian theorem for modules on a small ringed site. -/
@[instance] theorem actionGrothendieck : IsGrothendieckAbelian.{u + 1} (Equivariant A G) := by
  sorry

/-- Trivial action is additive and exact on the underlying modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: it leaves objects and maps unchanged and preserves the induced kernels and cokernels. -/
@[instance] theorem trivialAdditive : (trivial (R := A.toMon) (P := G)).Additive := by
  exact ⟨by intros; rfl⟩

/-- Exactness of trivial action, on kernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying kernel with trivial action is the equivariant kernel. -/
@[instance] theorem trivialLimits :
    PreservesFiniteLimits (trivial (R := A.toMon) (P := G)) := by
  let U := CondensedBar.forgetAction (A := A) (G := G)
  have : U.ReflectsIsomorphisms := forgetReflects A G
  have : PreservesFiniteLimits U := (forgetExact A G).1
  have : PreservesFiniteLimits (trivial (R := A.toMon) (P := G) ⋙ U) :=
    show PreservesFiniteLimits (𝟭 (Modules A)) from inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

/-- Exactness of trivial action, on cokernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying sheafified cokernel retains trivial action. -/
@[instance] theorem trivialColimits :
    PreservesFiniteColimits (trivial (R := A.toMon) (P := G)) := by
  let U := CondensedBar.forgetAction (A := A) (G := G)
  have : U.ReflectsIsomorphisms := forgetReflects A G
  have : PreservesFiniteColimits U := (forgetExact A G).2.1
  have : PreservesFiniteColimits (trivial (R := A.toMon) (P := G) ⋙ U) :=
    show PreservesFiniteColimits (𝟭 (Modules A)) from inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

variable {A G} {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of actions along a continuous group map is additive.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition changes no underlying map, hence preserves sums. -/
@[instance] theorem restrictionAdditive (v : H →ₜ* G) :
    (inflate (R := A.toMon) v).Additive := by
  exact ⟨by intros; rfl⟩

/-- Restriction is left exact, with the induced action on the same kernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with the kernel construction. -/
@[instance] theorem restrictionLimits (v : H →ₜ* G) :
    PreservesFiniteLimits (inflate (R := A.toMon) v) := by
  let U := CondensedBar.forgetAction (A := A) (G := H)
  have : U.ReflectsIsomorphisms := forgetReflects A H
  have : PreservesFiniteLimits U := (forgetExact A H).1
  have : PreservesFiniteLimits (inflate (R := A.toMon) v ⋙ U) :=
    show PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) from
      (forgetExact A G).1
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

/-- Restriction is right exact, with the induced action on the same cokernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with sheafified cokernels. -/
@[instance] theorem restrictionColimits (v : H →ₜ* G) :
    PreservesFiniteColimits (inflate (R := A.toMon) v) := by
  let U := CondensedBar.forgetAction (A := A) (G := H)
  have : U.ReflectsIsomorphisms := forgetReflects A H
  have : PreservesFiniteColimits U := (forgetExact A H).2.1
  have : PreservesFiniteColimits (inflate (R := A.toMon) v ⋙ U) :=
    show PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) from
      (forgetExact A G).2.1
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

section Derived
variable [HasDerivedCategory.{u + 1} (Modules A)]
  [HasDerivedCategory.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 1} (Equivariant A H)]

end Derived

variable {A' : CondensedBar.Ring.{u}}

end CategoryTheory.CondensedDerivedRestriction
