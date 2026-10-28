/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates

/-! Compatibility of finite pullback compositors with fixed coefficient realization.
Source: the first paragraph of the proof of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The prescribed pullback compositor becomes the canonical fixed-coefficient
compositor. There is no tensor product or Tor-amplitude hypothesis in this assertion.

Source: the coefficient-realization calculation in the first paragraph of
the blueprint proof of `prop-sf-pf-coherence` (first paragraph).
(blueprint: lem-sf-finite-pullback-composition-fixed-coordinates).

Proof: apply the inverse coefficient realization at X to
`S.finitePullCompositionNormalization f g M`. Expand `fixedPullRealization` as the
inverse realization applied to `pullRealization`, followed by the inverse realization
unit and the inverse of `fixedPullComparison`. The two exact-functor composition
comparisons in `pullRealization` identify the intrinsic pullback with the conjugate
of fixed-scalar exact pullback. Naturality moves these comparisons past the realized
map for g. The associativity identity for `mapDerivedCategoryCompIso`, together with
its compatibility with `mapDerivedCategoryNatIso` and whiskering, identifies the
image of `sfIntrinsicDerivedPullbackComp` with the fixed-scalar exact compositor;
the middle coefficient unit inserted by `sfIntrinsicTransportComp` cancels the
inverse unit occurring in `fixedPullRealization`. Finally expand
`leftDerivedUpperStarComp` using the exact-to-left-derived comparison. Its two
comparison factors cancel the two `fixedPullComparison` factors on the left,
leaving the displayed right-hand side. All cancellations are of the specified
realization units and exact-to-derived comparisons, so no alternative compositor
or coefficient equivalence is chosen. -/
theorem pullbackComposition_fixed_coordinates
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : sixFunctorFiniteCategory D C E n hn Z) :
    let A := ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
        ((S.finite.pullComposition f g).hom.app M) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj M)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (fixedPullRealization S g M).hom =
    (fixedPullRealization S (f ≫ g) M).hom ≫
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp A f.hom.left g.hom.left).hom.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) Z).obj M) := by sorry

end WeilConjectures.CompactSupportFiniteProjection
