/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTraceConstruction

/-!
# Open counit compatibility for the standard affine-line exchange
Source: blueprint sk-prop-an, Step 5(b), detailed trace proof step 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The standard compact-support exchange respects the open counit before the
projective trace is applied.
Source: blueprint lem-amb-affine-space-top-trace, proof step 8
(blueprint: lem-amb-affine-trace-line-open-counit-base-change).

Proof: first work with the pulled-back projective compactification. Expand its
exchange as proper direct-image exchange followed by inverse open exchange.
The identity unit_map_derivedOpenImmersionLowerShriekBaseChangeIso says that open
exchange is the mate of the pullback square. Apply the open adjunction hom-equivalence
to the two proposed counit composites: both become the same pullback-square map by
the unit-counit triangle identity. Thus the open square commutes on every M.
Naturality of proper direct-image exchange moves the old open counit through the
proper factor. Transport the resulting square from the pulled-back projective
compactification to the standard one. The comparison is the composite through a
common refinement of the proper/open unit, inverse open exchange and direct-image
composition. The units and composition comparisons cancel by their triangle and
pasting identities, giving the displayed square for the actual chosen comparison.
The inverse-image comparisons from derived to exact inverse image are natural, so
the same equation holds for the left-derived pullbacks in this statement.
This is a formal mate identity; it applies to arbitrary unbounded M and includes
identity base change, empty schemes and zero coefficients. No Tate datum or
projective trace is used. -/
theorem affineTraceLineExchange_openCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    let J := affineTraceOpenAdjunction A S
    let J' := affineTraceOpenAdjunction A S'
    affineTraceLineExchange A g
        ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj M) ≫
      (affineTraceLineLeft A S').map ((affineTraceOpenPullbackSquare A g).hom.app M) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (J'.counit.app ((ordinaryFinitePullback A
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj M)) =
    (ordinaryFinitePullback A g).map
      ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map (J.counit.app M)) ≫
        ordinaryFiniteP1Exchange A g M := by
  sorry

end AlgebraicGeometry.Etale
