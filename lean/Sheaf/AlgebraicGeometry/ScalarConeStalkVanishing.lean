/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Stalk vanishing for a scalar cone

Source: Stacks Project, Tags 08EK and 05QR
(blueprint: lem-sc-scalar-cone-stalk-vanishing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A single scalar cone has zero cohomology stalks at a point where the scalar
is invertible, or where its input already has zero cohomology stalks in every degree.
Source: Stacks Project, Tag 08EK, cone construction, and Tag 05QR
(blueprint: lem-sc-scalar-cone-stalk-vanishing).

Proof: Apply the exact stalk functor to a representative of the distinguished
triangle. Exactness identifies the cohomology of the stalk complex with the stalks
of the cohomology sheaves. Scalar multiplication becomes multiplication by the
germ of the compatible global section. If x belongs to the basic open of its top
section, this germ is a unit in the local ring, hence gives an isomorphism of stalk
complexes and of their cohomology. The long exact cohomology sequence then makes
all cone cohomology groups zero (equivalently, use Tag 05QR after derived stalk).
In the second case both copies of the input are acyclic at x; exactness gives zero
cone cohomology in every degree regardless of the scalar. A zero module has a
subsingleton underlying type. -/
theorem scalar_cone_stalk_vanishing (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E K : schemeDerivedCategory X) (b : E ⟶ K) (d : K ⟶ E⟦(1 : ℤ)⟧)
    (hcone : Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d ∈
      distTriang (schemeDerivedCategory X)) (x : X)
    (hx : x ∈ X.basicOpen (g.val (op ⊤)) ∨
      ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) :
    ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x)) := by
  sorry

end AlgebraicGeometry.Scheme
