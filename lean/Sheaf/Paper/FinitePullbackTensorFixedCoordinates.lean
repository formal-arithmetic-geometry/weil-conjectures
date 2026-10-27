/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module
public import Sheaf.Paper.FiniteProjectionFixedCoordinates

/-! # Pullback tensor comparison in fixed coefficient coordinates

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
/-- The prescribed pullback/tensor comparison in fixed coefficient coordinates.
Source: prop-sf-pf-coherence, proper-factor paragraph, and the explicit construction
of pullbackTensorComparison (blueprint: lem-sf-finite-pullback-tensor-fixed-coordinates).
Proof: expand pullbackTensorComparison as the pullback realization followed by the
coefficient realization of the fixed scalar tensor pullback comparison. Apply the inverse
realization. Naturality of its inverse unit moves the inner fixed scalar map past the
unit. The second-input fixed pullback comparison and its inverse cancel after applying
tensor in that input. The first-input comparison remains inverted. Functoriality and
associativity give exactly the displayed composite. No properness, counit, projection,
or finite Tor condition on the first input is used. Zero objects and empty schemes use
the same unit and isomorphism identities. -/
theorem pullbackTensor_fixed_coordinates (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        (pullbackTensorComparison S f M L).hom ≫
      (targetCoordinates S f ((S.finite.pull f).obj M) L).hom =
    (fixedPullRealization S f (((partialTensor S Y).obj M).obj L)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (tensorCoordinates S Y M L).hom ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) Y).obj M)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) ≫
      ((fixedTensor (C := C) (E := E) (n := n) X).map
        (fixedPullRealization S f M).inv).app
          ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
            ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) := by
  sorry

end WeilConjectures.CompactSupportFiniteProjection
