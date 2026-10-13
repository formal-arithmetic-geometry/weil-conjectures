/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Compatible tensor shifts for derived pullback

Source: Stacks Project, Tag 08EU, proof, and Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-derived-pullback-tensor-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Tensor shift comparisons can be chosen naturally in the fixed tensor factor,
exactly, and compatibly with the supplied strong monoidal derived pullback.
Source: Stacks Project, Tag 08EU, proof, and Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-derived-pullback-tensor-shift).

Proof: compute the derived tensor on K-flat complexes. Translation in the first
factor has its usual Koszul comparison, natural in the second factor, and tensoring
preserves mapping cones. Compute pullback by termwise tensor pullback of K-flat
resolutions. The comparison of pullback with translation identifies the shifted
inverse tensorator with the inverse tensorator followed by the tensor shift
comparisons. For a supplied strong monoidal structure, transport these comparisons
using its tensorator and unit isomorphism: write translation as tensoring with the
translated unit. Associativity of the tensorator identifies the two iterated
comparisons, and its unit identities give the comparison for translation by zero.
Transport along the resulting natural isomorphisms preserves distinguished
triangles. Naturality in the fixed factor gives shift compatibility of every
morphism of tensor functors. Descend the comparisons and their zero and addition
identities through the K-flat localization. Choose the pullback shift together with
the tensor shifts, imposing no independently fixed shift comparison. No direct
image, adjunction, counit, or projection mate is involved. Empty schemes and the
zero tensor factor are included,
since tensor and all comparison isomorphisms restrict to the zero category. -/
theorem derivedPullback_tensorShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ) ∧
      (∀ M : schemeDerivedCategory Y,
        NatTrans.CommShift
          (F₁ := tensorRight M ⋙ derivedPullback f)
          (F₂ := derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M))
          ((Functor.flipping.functor.map
            (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))).app M) ℤ) := by sorry

end AlgebraicGeometry
