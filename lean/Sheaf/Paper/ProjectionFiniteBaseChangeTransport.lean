/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization
import all Sheaf.Paper.FiniteProjectionExchangeTransposes

/-! # Reflecting the realized finite base-change square

Source: prop-sf-pf-coherence, base-change paragraph.
(blueprint: lem-sf-finite-base-change-transport).
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

private theorem reflectProjectionPaths
    {A B : Type*} [Category A] [Category B] (I : A ⥤ B) [I.Faithful]
    {X Y : A} {X' Y' : B} (s : I.obj X ≅ X') (t : I.obj Y ≅ Y')
    (a b : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha : I.map a ≫ t.hom = s.hom ≫ a')
    (hb : I.map b ≫ t.hom = s.hom ≫ b') (h : a' = b') : a = b := by
  apply I.map_injective
  apply (cancel_mono t.hom).mp
  exact ha.trans ((congrArg (fun z ↦ s.hom ≫ z) h).trans hb.symm)

/-- The two constructible routes agree by faithful realization of the canonical diamond.
Source: prop-sf-pf-coherence, base-change paragraph
(blueprint: lem-sf-finite-base-change-transport).

Proof: the separate route-realization equations have the same source and target
comparison isomorphisms. The canonical fixed-scalar diamond identifies their right
sides. Cancel the target isomorphism and use faithfulness of the full inclusion.
No inverse of a projection or exchange is used, and no separatedness of g is needed. -/
theorem sixFunctorProjectionFinite_baseChange_transport
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    sixFunctorProjectionFiniteLeftPath S Q K L =
      sixFunctorProjectionFiniteRightPath S Q K L := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let R' := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  obtain ⟨hl, hr⟩ := sixFunctorProjectionFinite_routes_realization S Q K L
  exact reflectProjectionPaths
    (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    (sixFunctorProjectionFiniteSquareSource S Q K L)
    (sixFunctorProjectionFiniteSquareTarget S Q K L)
    (sixFunctorProjectionFiniteLeftPath S Q K L)
    (sixFunctorProjectionFiniteRightPath S Q K L) _ _ hl hr
    (congrArg R'.functor.map
      (FiniteProjectionExchange.diamond_equality A Q.square Q.compactification
        (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)))

end WeilConjectures
