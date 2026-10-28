/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates
import Sheaf.Paper.ConstructibleProjectionMates

/-! # Coordinate projection equation for proper normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/--
The coordinate image of the expanded proper component is the fixed direct-image
projection map after the source and target tensor comparisons.  This is the
coefficient-normalization part of the proper-factor calculation: expand the
proper identity, use `finiteProperNormalization`, and cancel the realization
units and the direct/tensor comparison isomorphisms.  The remaining adjunction
transpose is handled by the theorem in the importing module.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-proper-projection-fixed-realization-normalization)
Proof: expand `properComponent` and `component`; apply the finite proper
normalization and the normalized direct adjunction mate.  Naturality of the
realization unit and of the tensor comparison cancels the coefficient units,
leaving the fixed direct-image projection map on the displayed object.
The identity compactification, identity inputs, and zero morphisms reduce by
functoriality and the unit/counit identities.
-/
theorem properComponent_fixed_realization_coordinate_projection
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let pc :=
      ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
        component S f (.ofIsProper f.hom.left) K L ≫
        (S.finite.properIdentity f).hom.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map pc ≫
        (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
        (fixedDirect (C := C) (E := E) (n := n) f).map (targetCoordinates S f K L).hom =
      (directTensorCoordinates S f K L).hom ≫
      ((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) := by
  sorry

end WeilConjectures.CompactSupportFiniteProjection
