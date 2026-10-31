/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapAssoc

/-! # Tensor counit square for the specified affine-chart open adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The specified inverse open projection and its two swaps obey the derived counit
square, with the ordinary derived pullback as right adjoint.
Source: Stacks Tag 0GL1 and the canonical exact/left-derived comparison
(blueprint: lem-pur-derived-open-counit-tensor-action).

Proof: transport the derived exact open adjunction by its canonical right comparison.
The mixed tensorator in the existing projection is the transported tensorator, so
TensorProjectionRightTransport identifies its projection with the ordinary one.
The abstract openCounit_tensorAction then gives the equality, since derived pullback
is braided. Every symmetry is the canonical signed derived symmetry. -/
theorem derivedOpenCounit_tensorAction
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (H M : DerivedCategoryModule A (ProjectiveLine S)) :
    OrdinaryAffineTensorActions.openAction A S H
        ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj M) ≫
      (affineTraceOpenLeft A S).map
        (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart S) H M).symm.hom ≫
      (affineTraceOpenAdjunction A S).counit.app
        (((ordinaryFiniteTensor A (ProjectiveLine S)).obj H).obj M) =
      ((ordinaryFiniteTensor A (ProjectiveLine S)).obj H).map
        ((affineTraceOpenAdjunction A S).counit.app M) := by
  sorry

end AlgebraicGeometry.Etale
