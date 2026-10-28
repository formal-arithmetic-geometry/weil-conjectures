/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates

/-! # Fixed-scalar coordinates of the right projection diamond

The definition is compared with the exposed fixed-category tensor and projection API.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Fixed-category coordinates of the right diamond, for arbitrary derived inputs.
Source: prop-sf-pf-coherence.proof.md, displayed right-diamond composite.
(blueprint: lem-sf-finite-projection-diamond-right-fixed-coordinates).

Proof: unfold `diamondRight` and `tensorMap`. Functoriality sends the identity
in the second tensor argument to an identity, which cancels. The tensor comparison
is the published `leftDerivedUpperStarTensorIso`. The compactly supported functor
is the open/proper composite defining `sfFixedCompactSupport`; the pullbacks are
`fixedDerivedPull`. Finally `projectionTensorCoordinateComponent_eq` identifies
the last factor with `fixedComponent`. These substitutions give the displayed
three factors. No constructibility, finite-Tor, or invertibility of exchange or
projection is used.
-/
theorem finiteProjectionDiamondRight_fixed_coordinates
    (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (Sheaf (ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Q.Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    FiniteProjectionExchange.diamondRight A Q.square Q.compactification K L =
      (leftDerivedUpperStarTensorIso (ModuleCat A) Q.g.hom.left
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
          Q.compactification).obj K) L).hom ≫
        ((fixedTensor (C := C) (E := E) (n := n) Q.Y').map
          (FiniteProjectionExchange.ex A Q.square Q.compactification K)).app
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj L) ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
          (Q.compactification.ofIsPullback Q.square)
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj K)
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj L) := by
  sorry

end WeilConjectures
