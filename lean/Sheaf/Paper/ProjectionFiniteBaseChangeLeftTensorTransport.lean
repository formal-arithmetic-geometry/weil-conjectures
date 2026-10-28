/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates

/-! # Tensor and pullback comparisons at the end of the left base-change route

Source: prop-sf-pf-coherence.proof.md, base-change paragraph, tensor identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures
open CompactSupportFiniteProjection
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The final tensor/pullback transport of the left route has its fixed-scalar target.
This assertion contains no projection component and no exchange map.

Source: prop-sf-pf-coherence.proof.md, base-change paragraph, canonical monoidality
and pullback-square comparisons; finitePullCompositionNormalization.
(blueprint: lem-sf-finite-base-change-left-tensor-transport).

Proof: move the tensor transport across supportRealization by naturality. Expand Mu
and cancel its inverse fixed-pull comparisons against the target tensor comparisons.
Naturality of the coefficient equivalence unit cancels the remaining tensor unit.
Use finitePullCompositionNormalization on each of the two restricted compositors.
The equality transport for Q.squareComm then gives the inverse canonical derived
square comparison. More explicitly, write r_h for fixedPullRealization along h and
tau for the displayed restricted square transport. In inverse realization coordinates,
tau followed by r_f' at g-star L and f'-star of r_g equals r_g' at f-star L,
then g'-star of r_f, then the inverse fixed square comparison. This follows by
applying the two normalization equations, cancelling their common composite-map
pullback realization, and transporting that realization along Q.squareComm.
Tensor this equation with the fixed first input. Naturality of the canonical
monoidality map moves r_f through it, giving the fixed-scalar target. This calculation
uses only invertible coordinate comparisons, and is valid for zero inputs, identity
maps and empty schemes. No finite-Tor assumption on the first input is used. -/
theorem sixFunctorProjectionFinite_left_tensor_transport
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
      R'.functor.mapIso (F.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ U.mapIso d))
    I.map ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
      ((sixFunctorProjectionFiniteMu S Q.g' K
          ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)).hom ≫
        ((partialTensor S.toSixFunctorFiniteOperations Q.X').obj
          ((S.finite.pull Q.g').obj K)).map
          ((torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
            ObjectProperty.homMk (eqToHom (congrArg
              (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj)
              Q.squareComm)) ≫
            (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom))) ≫
      (sixFunctorProjectionFiniteSquareTarget S Q K L).hom =
    mid.hom ≫ R'.functor.map (F.map
      (FiniteProjectionExchange.target A Q.square (RX.inverse.obj K.obj)
        (RY.inverse.obj L.obj))) := by sorry

end WeilConjectures
