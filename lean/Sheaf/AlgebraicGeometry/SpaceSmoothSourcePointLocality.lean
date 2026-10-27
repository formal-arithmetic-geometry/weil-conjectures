/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Smoothness at a point and smooth source maps of algebraic spaces

Source: Stacks Project, Descent on Spaces, Tags 06F2 and 06ER;
Morphisms of Spaces, Tags 03ZD, 03ZE and 042S
(blueprint: lem-sfb-space-smooth-source-point-locality).

Smoothness at a point is expanded as smoothness on an open subspace containing it.
The chart condition is tested on every compatible étale presentation. Open subspaces,
point classes and the canonical map on points are the existing project constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Precomposition by a smooth space map preserves and reflects smoothness at each
source point. Neither surjectivity of `q` nor any regularity hypothesis on `h` is assumed.

Source: Stacks Project, Descent on Spaces, Tags 06F2 and 06ER, with the definition of
properties local on the source; Morphisms of Spaces, Tags 03ZD, 03ZE, 04TA and 042S
(blueprint: lem-sfb-space-smooth-source-point-locality).

Proof:
1. Open subspace inclusions are representable étale, hence smooth. The chart and
representable conventions agree: use the étale presentation criterion in both directions
and smooth base change (lem-sfb-space-etale-presentation-property-criterion,
lem-sfb-scheme-etale-source-target-properties,
lem-sfb-space-smooth-surjective-fppf-locality,
lem-sfb-fibred-groupoid-representable-smooth-calculus). If h is smooth on A around q(z),
the open pullback Z_A contains z and its map to Y is smooth by base change and composition
(lem-a1-space-open-factor-scheme-tests, lem-trf-space-fibre-products-etale-covers,
lem-weil-pbc-etale-composition-cancellation).
2. Conversely choose an open W around z where hq is smooth. Its map q_W to X is smooth,
hence flat and locally finitely presented by lem-sfb-stack-chartwise-smooth-etale-calculus.
Its point image is open by lem-sfb-flat-lfp-space-universally-open. The open-subspace
correspondence of lem-a1-space-etale-open-image gives O in X with precisely that image.
By lem-a1-space-open-factor-scheme-tests, q_W factors through O as a smooth surjective
map r : W to O, since this factor is the base change of q_W. Put g = h restricted to O;
then gr is smooth.
3. Choose surjective étale scheme atlases V to Y and U to O times_Y V. Choose a
surjective étale scheme atlas T of W times_O U. Then p : T to U is smooth and surjective,
and c : T to W is étale, by lem-trf-space-fibre-products-etale-covers and the
representable calculus. If d : U to V and b : V to Y are the chart maps, their square
satisfies b composed with dp = gr composed with c.
4. The étale presentation criterion and scheme étale source-and-target locality show
that dp is smooth. The smooth scheme map p is flat, surjective and locally finitely
presented, so lem-sbc-smooth-flat-surjective-source-descent (Stacks 05B5) makes d smooth.
The presentation criterion then makes g smooth, without an advance hypothesis on g.
5. Since z lies in W, q(z) lies in O, so O witnesses smoothness of h at q(z).
The original q need not be surjective: O can be a proper open of X. If Z is empty,
there are no points to test. No flatness or finite-presentation hypothesis on h was used. -/
theorem smooth_at_iff_of_smooth_source {B : Scheme.{u}} {X Y Z : AlgebraicSpace B}
    (h : X ⟶ Y) (q : Z ⟶ X) (hq : MapIsLocally (@Smooth) q)
    (z : Point Z.obj.obj) :
    (∃ W : OpenSubspace Z, z ∈ pointImage W.val.ι ∧
      ∀ (U V : Over B) (a : yoneda.obj U ⟶ W.val.toFunctor)
        (b : yoneda.obj V ⟶ Y.obj.obj) (k : U ⟶ V),
        IsEtale a → IsEtale b →
          a ≫ (W.val.ι ≫ (q ≫ h).hom.hom) = yoneda.map k ≫ b → Smooth k.left) ↔
    (∃ A : OpenSubspace X, mapPoint q.hom.hom z ∈ pointImage A.val.ι ∧
      ∀ (U V : Over B) (a : yoneda.obj U ⟶ A.val.toFunctor)
        (b : yoneda.obj V ⟶ Y.obj.obj) (k : U ⟶ V),
        IsEtale a → IsEtale b →
          a ≫ (A.val.ι ≫ h.hom.hom) = yoneda.map k ≫ b → Smooth k.left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
