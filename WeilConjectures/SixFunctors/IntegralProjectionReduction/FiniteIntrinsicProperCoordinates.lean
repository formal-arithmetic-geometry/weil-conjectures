/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteProjectionCoordinateMate
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicAdjunctionRealization
import WeilConjectures.SixFunctors.Finite.FiniteIntrinsicPullbackNormalization

/-! # Proper projection in inverse coefficient coordinates

Source: fix-prop-projection-formula.proof.md; Stacks 07A4, 07A5 and 0B56.
(blueprint: lem-sf-finite-intrinsic-proper-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CompactSupportFiniteProjection.realization sixFunctorFiniteRealization
  integralCoefficientSheaf integralCoefficientCommRingSheaf

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Inverse realization carries the proper counit mate to the fixed proper mate.
Source: fix-prop-projection-formula.proof.md, same-map sentence; Stacks 07A4, 07A5, 0B56.
(blueprint: lem-sf-finite-intrinsic-proper-coordinates).

Proof: first identify the actual intrinsic and fixed adjunction units and counits
using the section-normalized scalar inverse mate and the K-injective-normalized
direct-image comparison. The inversePullback and inverseDirectImage comparisons
therefore preserve both units and counits. On simultaneous flat K-flat tensor
representatives, the scalar tensor/pullback square is the balanced section map
finiteScalarTensorPullback_onRepresentatives. Descend it and conjugate it by the
unit-preserving pullback realization and coefficient counits; this gives the square
between inverseTensor and inversePullback. Apply the Hom bijection for the fixed
pullback/direct-image adjunction to the displayed equation. The transpose of the
intrinsic proper map is canonicalFinitePullbackTensor followed by the intrinsic
counit tensored with identity. The preceding two equations identify this with the
fixed transpose. Tensor naturality moves openCoordinate to the first factor;
naturality of the fixed projection moves the map induced by l to the output.
Adjunction injectivity and coefficient-equivalence faithfulness give the result.
Expanding midpoint identifies its target coordinate composite: naturality of
inversePullback with l moves its map through the exact localization compositors,
then the exact-to-left-derived comparison and coefficient unit give the displayed
map. The source is left in inverse coefficient coordinates. No S.finiteSupport or
sourceComparison normalization is involved.
The argument uses no invertibility of the proper projection and applies to zero
objects and empty schemes as well as m = 0. -/
theorem intrinsic_proper_coordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RY := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Y
    let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let R := proEtaleConstantDerivedDirectImage c.g A
    let Rf := (lowerStar B c.g).rightDerivedFunctor
    let TY := Functor.uncurry.obj (derivedTensor B Y.obj.left)
    let pj := FiniteIntrinsicRealization.openCoordinate (C := C) (E := E) m f c K U k
    let er := FiniteIntrinsicRealization.inverseDirectImage (C := C) (E := E) m Q.p
    (SystemProjectionFormula.finiteProperProjection C.l E D C.different c.g
      (c.g ≫ Y.obj.hom) Y.obj.hom m
      (((sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory).obj U) V) ≫
        midpoint m f c K L U V k l =
      (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
          (R.obj (J.obj U), V) ≫
        RY.functor.map (TY.map (Prod.mkHom
          (er.hom.app (J.obj U) ≫ Rf.map pj.hom) (RY.inverse.map l.hom))) ≫
        fixedProper m f c K L := by sorry

end WeilConjectures.IntegralProjectionReduction
