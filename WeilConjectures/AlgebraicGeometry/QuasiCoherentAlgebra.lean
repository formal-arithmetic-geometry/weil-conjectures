/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

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

end AlgebraicGeometry
