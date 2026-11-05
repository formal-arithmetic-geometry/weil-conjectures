/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.Algebra.Homology.KFlatConeTrianglePresentation
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonConeRows
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare

/-! # Exact five-term diagrams for localized tensor comparison

Source: Stacks Project, Tags 06Y6, 0BYJ and 0DJA(1).
(blueprint: lem-pc-localized-tensor-comparison-triangle-five-term-diagram).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

end ModuleCat
