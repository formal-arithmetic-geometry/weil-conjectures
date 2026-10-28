/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

/-! The distinguished-triangle package for the finite-free scalar projection.
(blueprint: lem-sfb-finite-free-scalar-projection-triangle)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/--
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, finite free and
finitely presented coefficient extensions, cone paragraph; Stacks Tag 0944.

The finite-free point-module identifications make the coefficient projection
transformation additive on the two degree-zero finite biproduct terms.  Exactness
of the tensor/direct-image composite makes it send the mapping-cone triangle of
`S.f` to a distinguished triangle.  The first two components are the finite
biproduct maps and are isomorphisms, while the third component is the displayed
`projection` after the specified `modelPull` identification.  This theorem
records precisely that triangle package; the final isomorphism follows by the
triangle two-out-of-three lemma.
(blueprint: lem-sfb-finite-free-scalar-projection-triangle)
-/
theorem finiteFreeScalarProjection_triangle
    (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ)) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    ∃ (T T' : Triangle (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)))
      (φ : T ⟶ T'),
      T ∈ distTriang (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) ∧
      T' ∈ distTriang (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) ∧
      T.obj₃ = DerivedCategory.Q.obj (complex Λ S Y) ⊗
        (moduleObjectDerivedPushforward Λ.X f).obj K ∧
      T'.obj₃ = (moduleObjectDerivedPushforward Λ.X f).obj
        (DerivedCategory.Q.obj (complex Λ S X) ⊗ K) ∧
      IsIso φ.hom₁ ∧ IsIso φ.hom₂ ∧
      ∀ (hY : T.obj₃ = DerivedCategory.Q.obj (complex Λ S Y) ⊗
          (moduleObjectDerivedPushforward Λ.X f).obj K)
        (hX : T'.obj₃ = (moduleObjectDerivedPushforward Λ.X f).obj
          (DerivedCategory.Q.obj (complex Λ S X) ⊗ K)),
        eqToHom hY.symm ≫ φ.hom₃ ≫ eqToHom hX =
          projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
            (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
