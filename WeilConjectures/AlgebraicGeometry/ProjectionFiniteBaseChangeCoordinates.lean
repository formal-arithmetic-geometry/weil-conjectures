/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.FiniteProjectionExchangeData

/-! # Finite projection base-change coordinates

Source: prop-sf-pf-coherence, the realization of its displayed base-change square.
(blueprint: def-sf-finite-base-change-realization-paths).
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
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Inverse realization of the finite partial tensor, with its coefficient unit cancelled.
Source: current blueprint prop-sf-pf-coherence, tensor identifications
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteTensorRealization (_S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :=
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  (R.unitIso.app
    (((CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X).obj
      (R.inverse.obj K.obj)).obj (R.inverse.obj L.obj))).symm

/-- Monoidality on the finite partial-tensor domain, in the datum's operation coordinates.
Source: current blueprint prop-sf-pf-coherence, vertical tensor comparison
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (S.finite.pull f).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).obj
        K).obj L) ≅
    ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
      ((S.finite.pull f).obj K)).obj
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations f).obj L) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X
  let U := CompactSupportFiniteProjection.fixedDerivedPull (C := C) (E := E) (n := n) f
  ObjectProperty.isoMk _
    (CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations f
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).obj
        K).obj L) ≪≫
      RX.functor.mapIso
        ((CompactSupportFiniteProjection.fixedPullComparison
          (C := C) (E := E) (n := n) f).symm.app _ ≪≫
          U.mapIso (sixFunctorProjectionFiniteTensorRealization S Y K L) ≪≫
          AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
            f.hom.left (RY.inverse.obj K.obj) (RY.inverse.obj L.obj) ≪≫
          (TX.mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations f K).symm).app _ ≪≫
          (TX.obj _).mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations f ⟨L.obj, L.property.1⟩).symm))

/-- The A2 finite exchange in the actual bounded constructible operation coordinates.
The target uses the Cartesian base change of the chosen compactification; arbitrary
choices are compared by sixFunctorProjection_compactification.
Source: current blueprint prop-sf-pf-coherence, Ex_! vertical arrow
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteExchange (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D) (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    (S.finite.pull Q.g).obj ((S.finite.support Q.f Q.compactification).obj K) ⟶
      (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
        ((S.finite.pull Q.g').obj K) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let U := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  ObjectProperty.homMk
    ((CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations Q.g
      ((S.finite.support Q.f Q.compactification).obj K)).hom ≫
      R.functor.map (U.map (CompactSupportFiniteProjection.fixedSupportRealization
        S.toSixFunctorFiniteOperations Q.f Q.compactification K).hom) ≫
      R.functor.map
        ((CompactSupportFiniteProjection.fixedPullComparison
          (C := C) (E := E) (n := n) Q.g).inv.app _) ≫
      (S.finiteExchangeProjection Q).2.1.app K ≫
      R.functor.map (F.map (CompactSupportFiniteProjection.fixedPullRealization
        S.toSixFunctorFiniteOperations Q.g' K).inv) ≫
      (CompactSupportFiniteProjection.supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)).inv)

/-- One ordered route in the finite projection/base-change square.
Source: prop-sf-pf-coherence, displayed square
(blueprint: def-sf-finite-base-change-realization-paths). -/
def sixFunctorProjectionFiniteLeftPath (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    (S.finite.pull Q.g).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L) ⟶
    (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X').obj
        ((S.finite.pull Q.g').obj K)).obj
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.f').obj
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L))) :=
  (S.finite.pull Q.g).map
      (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations
        Q.f Q.compactification K L) ≫
      sixFunctorProjectionFiniteExchange S Q
        (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X).obj
          K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
            Q.f).obj L)) ≫
      (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
        ((sixFunctorProjectionFiniteMu S Q.g' K
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.f).obj
            L)).hom ≫
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X').obj
            ((S.finite.pull Q.g').obj K)).map
            ((CompactSupportFiniteProjection.torPullComposition S.toSixFunctorFiniteOperations
              Q.g' Q.f L).inv ≫
              ObjectProperty.homMk (eqToHom (congrArg
                (fun f ↦ ((CompactSupportFiniteProjection.torPull
                  S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
              (CompactSupportFiniteProjection.torPullComposition S.toSixFunctorFiniteOperations
                Q.f' Q.g L).hom))

/-- One ordered route in the finite projection/base-change square.
Source: prop-sf-pf-coherence, displayed square
(blueprint: def-sf-finite-base-change-realization-paths). -/
def sixFunctorProjectionFiniteRightPath (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    (S.finite.pull Q.g).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L) ⟶
    (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X').obj
        ((S.finite.pull Q.g').obj K)).obj
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.f').obj
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L))) :=
  (sixFunctorProjectionFiniteMu S Q.g
      ((S.finite.support Q.f Q.compactification).obj K) L).hom ≫
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y').map
        (sixFunctorProjectionFiniteExchange S Q K)).app
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L) ≫
      CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L)

/-- The recorded source comparison for the whole base-change square.
Source: prop-sf-pf-coherence, vertical tensor identifications
(blueprint: def-sf-finite-base-change-realization-paths). -/
@[irreducible]
def sixFunctorProjectionFiniteSquareSource (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D)
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
  ((S.finite.pull Q.g).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L)).obj ≅ R'.functor.obj
    ((FiniteProjectionExchange.pull A Q.g.hom.left).obj
      (FiniteProjectionExchange.tensor A Q.Y.obj.left
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          Q.compactification).obj (RX.inverse.obj K.obj)) (RY.inverse.obj L.obj))) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let R' := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let U := CompactSupportFiniteProjection.fixedDerivedPull
    (C := C) (E := E) (n := n) Q.g
  CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations Q.g
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L) ≪≫
    R'.functor.mapIso
      ((CompactSupportFiniteProjection.fixedPullComparison
        (C := C) (E := E) (n := n) Q.g).symm.app _ ≪≫
      U.mapIso (R.inverse.mapIso (CompactSupportFiniteProjection.sourceComparison
        S.toSixFunctorFiniteOperations Q.f Q.compactification K L) ≪≫
        (R.unitIso.app _).symm))

/-- The recorded target comparison for the whole base-change square.
Source: prop-sf-pf-coherence, vertical tensor identifications
(blueprint: def-sf-finite-base-change-realization-paths). -/
@[irreducible]
def sixFunctorProjectionFiniteSquareTarget (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D)
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
  ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X').obj
        ((S.finite.pull Q.g').obj K)).obj
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.f').obj
          ((CompactSupportFiniteProjection.torPull
            S.toSixFunctorFiniteOperations Q.g).obj L)))).obj ≅
      R'.functor.obj
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Q.compactification.ofIsPullback Q.square)).obj
      (FiniteProjectionExchange.tensor A Q.X'.obj.left
        ((FiniteProjectionExchange.pull A Q.g'.hom.left).obj (RX.inverse.obj K.obj))
        ((FiniteProjectionExchange.pull A Q.f'.hom.left).obj
          ((FiniteProjectionExchange.pull A Q.g.hom.left).obj (RY.inverse.obj L.obj))))) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let R' := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let T' := CompactSupportFiniteProjection.fixedTensor
    (C := C) (E := E) (n := n) Q.X'
  let U' := CompactSupportFiniteProjection.fixedDerivedPull
    (C := C) (E := E) (n := n) Q.f'
  let F' := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  CompactSupportFiniteProjection.targetComparison S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
      ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L) ≪≫
    R'.functor.mapIso (F'.mapIso
      ((T'.mapIso (CompactSupportFiniteProjection.fixedPullRealization
        S.toSixFunctorFiniteOperations Q.g' K)).app _ ≪≫
      (T'.obj _).mapIso (U'.mapIso (CompactSupportFiniteProjection.fixedPullRealization
        S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩))))

end WeilConjectures
