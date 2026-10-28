/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.ConstructibleProjectionMates
public import Sheaf.SixFunctors.AmbientProperOpenCalculus

/-! # Unary pullback composition in fixed coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 2048

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFinitePullback
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor

/-- The operation pullback compositor realizes the canonical fixed-scalar compositor.
This is a unary normalization: no tensor, compact support or projection occurs.

Source: finitePullCompositionNormalization of def-sf-operation-stages and the
coefficient-unit cancellation in the composition clause of
fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-pullback-composition-realization).

Proof: apply inverse coefficient realization to finitePullCompositionNormalization.
Expand pullRealization using the two mapDerivedCategoryCompIso comparisons. Their
associativity and naturality identify the intrinsic compositor with the localization
of upperStarComp, with the inverse coefficient unit inserted between the two
pullbacks. Naturality of that unit moves the inner pullback comparison past it;
the adjacent unit and inverse cancel. Finally expand leftDerivedUpperStarComp:
its exact-to-left-derived comparisons cancel the fixedPullComparison factors
in fixedPullRealization. The pComp field of ordinary is this canonical compositor.
This leaves precisely the equation below. The argument
uses exact inverse image and works for every bounded constructible input, including
zero objects, empty schemes, identity morphisms and exponent one. -/
theorem fixedPullRealization_composition
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : sixFunctorFiniteCategory D C E n hn Z) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
        (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso
          (fixedPullRealization S g N)).hom =
    (fixedPullRealization S (f ≫ g) N).hom ≫
      ((ordinary D A).pComp f g).hom.app
        (RZ.inverse.obj N.obj) := by sorry

end WeilConjectures.CompactSupportFiniteProjection
