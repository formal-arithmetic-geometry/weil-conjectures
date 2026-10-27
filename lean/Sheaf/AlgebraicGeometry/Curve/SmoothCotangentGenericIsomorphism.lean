/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Cotangent line bundles and generic invertibility on smooth integral curves

Source: Stacks Project, `curves.tex`, Tag 0C1C, `lemma-generically-etale`, first paragraph
of the proof; `morphisms.tex`, Tags 02G1 and 02G2
(blueprint: lem-a1-smooth-curve-cotangent-generic-isomorphism).

The statement covers arbitrary morphisms over the field, including constant morphisms,
and arbitrary linear maps between the two specified cotangent line bundles.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Cotangent sheaves of smooth integral curves have rank one. A linear map from the pulled
back target cotangent sheaf to the source cotangent sheaf is nonzero exactly when its generic
stalk is nonzero, and exactly when it is invertible on a nonempty affine open. Restricted
cotangent stalks are nonzero free modules of rank one over the original source stalk ring.

Source: Stacks Project, Tag 0C1C, `lemma-generically-etale`, proof paragraph 1; Tags 02G1,
02G2, 0A21, 01ON and 01C8
(blueprint: lem-a1-smooth-curve-cotangent-generic-isomorphism).

Proof:
1. Apply `lem-sc-dimension-locally-algebraic` to each integral finite-type curve. Every
   nonempty open, hence every nonempty affine open, has dimension one, as does its dimension
   at every point. The sole fibre over Spec k is the curve itself. Smoothness therefore has
   relative dimension one (`def-sbc-smooth-morphisms`).
2. By `lem-sc-smooth-omega-finite-locally-free`, both cotangent sheaves are locally free of
   rank one. By `lem-weil-pbc-invertible-pullback-invertible`, the pullback along h is locally
   free of rank one too. This step requires no nonconstancy or smoothness of h.
3. On a common trivializing open T, a linear map is multiplication by a section a of O(T).
   Compatibility with restrictions gives the same formula on every smaller open and on
   stalks. If the generic stalk map is zero, a has zero generic germ. The injection of O(T)
   into the function field (`lem-sc-integral-scheme-stalks-in-function-field`) gives a = 0.
   Such T cover X; sheaf uniqueness gives u = 0. The converse follows by taking stalks.
4. If the generic stalk map is nonzero, a has a nonzero germ in the generic stalk field,
   hence a unit there. Its unit locus is an open neighbourhood of the generic point by
   `lem-weil-pbc-basic-open-function`, and multiplication by its inverse inverts the map.
   Choose an affine chart at the generic point (`def-pc-scheme`) and refine the intersection
   by a principal open (`lem-weil-pbc-spec-localization-away-basic-open`). This principal
   open is affine by clause (0) of `lem-weil-pbc-affine-ideals-closed-subscheme`.
5. Conversely the generic point belongs to every nonempty open of an integral scheme.
   An isomorphism on such an open gives an isomorphism on the generic stalk. In rank-one
   coordinates over the nonzero generic field, this map cannot be zero.
6. For a nonempty open W and x in W, restrict a rank-one local trivialization and take
   germs. Neighbourhoods contained in W are cofinal, so restriction does not change the
   stalk, including its scalar action. Thus the restricted stalk is isomorphic to O_{X,x}.
   This stalk ring is a nonzero domain by `lem-sc-integral-scheme-stalks-in-function-field`,
   so the module is nonzero. This applies to the generic point as well as closed points.
-/
theorem Scheme.Hom.smooth_curve_cotangent_generic_isomorphism
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsIntegralCurve pX] [IsIntegralCurve pY] [Smooth pX] [Smooth pY]
    (h : X ⟶ Y) (_w : h ≫ pY = pX) :
    (∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
      topologicalKrullDim (U : Set X) = 1) ∧
    (∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = 1) ∧
    SmoothOfRelativeDimension 1 pX ∧ SmoothOfRelativeDimension 1 pY ∧
    ((Scheme.Modules.tensorPullback h).obj pY.relativeDifferentials).IsInvertible ∧
    pX.relativeDifferentials.IsInvertible ∧
    (∀ (a : (Scheme.Modules.tensorPullback h).obj pY.relativeDifferentials ⟶
        pX.relativeDifferentials) (η : X), IsGenericPoint η Set.univ →
      (a ≠ 0 ↔
        (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj η).map a.val ≠ 0) ∧
      ((PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj η).map a.val ≠ 0 ↔
        ∃ V : X.Opens, (V : Set X).Nonempty ∧ IsAffineOpen V ∧
          IsIso ((Scheme.Modules.restrictFunctor V.ι).map a))) ∧
    (∀ W : X.Opens, (W : Set X).Nonempty → ∀ x : W,
      Nontrivial ((RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace x).obj
        (pX.relativeDifferentials.restrict W.ι)) ∧
      Nonempty
        ((ModuleCat.restrictScalars (W.ι.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace x).obj
            (pX.relativeDifferentials.restrict W.ι)) ≅
          ModuleCat.of (X.presheaf.stalk (W.ι x)) (X.presheaf.stalk (W.ι x)))) := by
  sorry

end AlgebraicGeometry
