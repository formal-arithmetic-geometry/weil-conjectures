/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenScalarTensorData

/-! # Tensor coherence of scalar extension and geometric pullback

Source: Stacks Project, Tags 07A4, 0D6D and 0E48.
(blueprint: lem-sf-scalar-pullback-tensor-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The balanced scalar/pullback comparison preserves the normalized tensorators.
This assertion concerns only the four left adjoints, without any projection formula.
Source: Stacks Project, Tags 07A4, 0D6D and 0E48
(blueprint: lem-sf-scalar-pullback-tensor-coherence).

Proof: choose flat-term K-flat representatives P and Q for the two inputs.
Scalar extension and geometric pullback preserve these resolving representatives.
The defining representative equations for the scalar tensorators and pullback
tensorators reduce both composites to maps of total tensor complexes. In bidegree
(p,q), both send 1 tensor (x tensor y) to the tensor of the two images of x and y
under the unit-normalized balanced scalar/pullback comparison. Balancing moves
all coefficients to this expression, and sheafification gives equality on each
summand. The maps preserve bidegrees, so their totalizations have identical signs.
Apply the localization functor and cancel the representative comparison
isomorphisms. Naturality along the resolution isomorphisms gives the equality
for arbitrary derived inputs. The generator and representative normalization
fields of Choices ensure this works for every choice, not just an existential
presentation. Empty sites, zero inputs and nonflat coefficient maps are included. -/
theorem scalarPullbackTensorCoherence (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (P Q : proEtaleDerivedCategory Y A) :
    (lambda m φ r).hom.app ((tensor m A Y).obj (P, Q)) ≫
        (scalar m φ Z).map ((restrictionTensor m A r).hom.app (P, Q)) ≫
        (c.scalarTensor φ Z).iso.hom.app
          ((constantPullback (A := A) r).obj P, (constantPullback (A := A) r).obj Q) =
      (constantPullback (A := B) r).map ((c.scalarTensor φ Y).iso.hom.app (P, Q)) ≫
        (restrictionTensor m B r).hom.app ((scalar m φ Y).obj P, (scalar m φ Y).obj Q) ≫
        (tensor m B Z).map
          (Prod.mkHom ((lambda m φ r).hom.app P) ((lambda m φ r).hom.app Q)) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenScalarTensor
