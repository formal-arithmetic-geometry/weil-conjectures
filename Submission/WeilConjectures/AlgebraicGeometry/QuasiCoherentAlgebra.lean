/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Quasi-coherent algebras and their affine-local properties

Source: Stacks Project, Properties, Section 28.23, Tags 05JS, 05JT, 086N and 0817
(blueprint: def-weil-pbc-quasi-coherent-algebra).

Algebra sheaves and their underlying modules reuse `Scheme.CommAlgebraSheaf`
and `Scheme.CommAlgebraSheaf.toModule`. Quasi-coherence uses Mathlib's existing
module-sheaf predicate. Finiteness, integrality and finite presentation are tested
on every affine open using the existing ring-homomorphism predicates.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

/-- A finite algebra sheaf has finite section algebras on every affine open.
Source: Stacks, Properties, definitions before Tag 086N
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsFinite {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.Finite

/-- An integral algebra sheaf has integral section algebras on every affine open.
Source: Stacks, Properties, definitions before Tag 086N
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsIntegral {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.IsIntegral

/-- Finite presentation as an algebra, rather than as a module, on every affine open.
Source: Stacks, Properties, definition before Tag 05JS
(blueprint: def-weil-pbc-quasi-coherent-algebra). -/
def Scheme.CommAlgebraSheaf.IsFinitePresentation {X : Scheme.{u}}
    (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.FinitePresentation

end AlgebraicGeometry
