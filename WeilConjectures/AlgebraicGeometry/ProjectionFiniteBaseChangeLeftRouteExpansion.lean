/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeLeftPrefix
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeLeftTensorTransport

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
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem assemble_left_route
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {x y z w : B} {a b c d : A}
    (p : x ⟶ y) (q : y ⟶ z) (r : z ⟶ w) (target : w ≅ R.obj d)
    (source : x ≅ R.obj a) (mid : z ≅ R.obj c)
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (hp : p ≫ q ≫ mid.hom = source.hom ≫ R.map (f ≫ g))
    (ht : r ≫ target.hom = mid.hom ≫ R.map h) :
    p ≫ q ≫ r ≫ target.hom = source.hom ≫ R.map (f ≫ g ≫ h) := by
  rw [ht, ← Category.assoc q, ← Category.assoc p, hp]
  simp only [Functor.map_comp, Category.assoc]

/-- Expansion of the first factor in the left route into the recorded source and
target comparisons.  This is the source-comparison/naturality subcalculation of
the base-change paragraph; its remaining proof is the cancellation of the
coefficient unit and counit and the normalized pullback compositor.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, first route.
(blueprint: lem-sf-finite-base-change-left-route-expansion).
-/
theorem sixFunctorProjectionFinite_left_route_expansion
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let source := sixFunctorProjectionFiniteSquareSource S Q K L
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map ((S.finite.pull Q.g).map
      (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations
        Q.f Q.compactification K L)) ≫
      I.map (sixFunctorProjectionFiniteExchange S Q
        (((CompactSupportFiniteProjection.partialTensor
          S.toSixFunctorFiniteOperations Q.X).obj K).obj
          ((CompactSupportFiniteProjection.torPull
            S.toSixFunctorFiniteOperations Q.f).obj L))) ≫
      I.map ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
        ((sixFunctorProjectionFiniteMu S Q.g' K
            ((CompactSupportFiniteProjection.torPull
              S.toSixFunctorFiniteOperations Q.f).obj L)).hom ≫
          ((CompactSupportFiniteProjection.partialTensor
              S.toSixFunctorFiniteOperations Q.X').obj
            ((S.finite.pull Q.g').obj K)).map
            ((CompactSupportFiniteProjection.torPullComposition
              S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
              ObjectProperty.homMk (eqToHom (congrArg
                (fun f ↦ ((CompactSupportFiniteProjection.torPull
                  S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
              (CompactSupportFiniteProjection.torPullComposition
                S.toSixFunctorFiniteOperations Q.f' Q.g L).hom))) ≫
      target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondLeft A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact assemble_left_route
    (CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y').functor
    _ _ _ _ _ _ _ _ _
    (sixFunctorProjectionFinite_left_prefix S Q K L)
    (sixFunctorProjectionFinite_left_tensor_transport S Q K L)

end WeilConjectures
