/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
import Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothing
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete

/-! # Stable smoothing with a prescribed ten-canonical frame

Source: Stacks Project, examples-defos.tex, Tag 0E7Y; moduli-curves.tex,
Tags 0E76 and 0E78; Morrison §3.3, Corollary 11(2), p.17.
(blueprint: lem-sfb-stable-curve-framed-trait-smoothing)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StableCurveFramedTrait

/-- The specified power-series trait as a k-scheme, using coefficient inclusion.
Source: Stacks 0E7Y (blueprint: lem-sfb-stable-curve-framed-trait-smoothing). -/
def base (k : Type u) [Field k] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (PowerSeries.C (R := k))))

/-- The special point uses the constant-coefficient map, with its actual k-structure.
Source: Stacks 0E7Y (blueprint: lem-sfb-stable-curve-framed-trait-smoothing). -/
def special (k : Type u) [Field k] : Over.mk (𝟙 (Spec (.of k))) ⟶ base k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) (by
    change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (PowerSeries.C (R := k))) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      PowerSeries.constantCoeff_comp_C, CommRingCat.ofHom_id, Spec.map_id])

/-- The generic point is induced by the canonical inclusion k[[t]] into k((t)).
Laurent series are the localization at t, not a separately chosen extension field.
Source: Stacks 0E7Y (blueprint: lem-sfb-stable-curve-framed-trait-smoothing). -/
def generic (k : Type u) [Field k] : Spec (.of (LaurentSeries k)) ⟶ (base k).left :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))

end AlgebraicGeometry.StableCurveFramedTrait

namespace AlgebraicGeometry

/-- Stable smoothing retaining the exact prescribed projective frame. The isomorphism
`c` identifies the base of the input family with Spec k, and `a` identifies the base of
its smoothing with the specified trait. Thus the family asserted over the trait is
literally the pullback along `a.hom.left`. Frames are those of the recorded complete
series; agreement of their complete embeddings expresses restriction of the frame.

Source: Stacks 0E7Y, 0E76, 0E78; Morrison §3.3, Corollary 11(2), p.17.
(blueprint: lem-sfb-stable-curve-framed-trait-smoothing)

Proof plan, following the eight steps of the node:
1. Stability gives a proper reduced pure-dimensional nodal curve. Properness is
   lem-trf-projective-bundle-proper. Apply lem-trf-nodal-curve-lci-criterion to obtain
   the lci property and unramifiedness of the first-Fitting singular subscheme.
2. By lem-trf-nodal-family-fitting-singular its support is exactly the nonsmooth locus.
   By lem-weil-pbc-unramified-over-field-discrete it is discrete. It is closed in a
   quasi-compact curve, hence finite; this includes the empty singular locus.
3. Apply lem-sfb-isolated-lci-curve-smoothing, retaining its special-fibre isomorphism,
   to obtain the projective flat finitely presented family and smooth generic fibre.
4. Use lem-kun-projective-implies-proper and
   lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous. The dimension-at-most-one
   open contains the closed point of the local trait, hence is the whole trait.
   Pass to geometric fibres by lem-sc-fibre-dimension-after-base-change. Apply
   lem-sfb-stable-and-smooth-family-open-loci; its stable-genus-g open also contains
   the closed point, hence is everything. Its universal property gives stability.
5. Apply lem-sfb-gorenstein-curve-relative-dualizing, including compatibility with the
   retained special-fibre isomorphism. Then lem-sfb-ten-canonical-hilbert-parameter
   gives the base-change-compatible rank-19(g-1) section module and closed evaluation.
6. By def-amb-finite-locally-free-module this module trivializes on a neighbourhood
   of the closed point, which is the whole local trait. Choose an initial frame.
7. By lem-sfb-projective-frames-pgl the difference from the prescribed special frame
   comes from GL_r(k), since r >= 19. Lift that matrix and its inverse as constant
   matrices to k[[t]]. Compose its projective action with the initial frame.
   Its reduction is exactly the prescribed frame, including in positive characteristic.
8. The framed complete embedding defines alpha by the representing property of
   lem-sfb-ten-canonical-hilbert-parameter. Its special point classifies (C,tau).
   Apply lem-sfb-stable-curve-pluricanonical-linear-series at n=10 to obtain generic
   degree 20(g-1). Stability already gives genus g; smoothness identifies arithmetic
   genus with the differential-form genus used by Scheme.Hom.genus.
-/
theorem stable_curve_framed_trait_smoothing
    (k : Type u) [Field k] [IsAlgClosed k] (g : ℕ)
    (P : TenCanonicalHilbert.Presentation k g)
    (C : StablePointedModuli (Spec (.of k)) g 0)
    (c : Over.mk (𝟙 (Spec (.of k))) ≅ C.base)
    (tau : TenCanonicalHilbert.Frame (P.series C) c.hom.left) :
    ∃ (X : StablePointedModuli (Spec (.of k)) g 0)
      (a : StableCurveFramedTrait.base k ≅ X.base)
      (phi : TenCanonicalHilbert.Frame (P.series X) a.hom.left)
      (e : pullback (pullback.snd X.projection a.hom.left)
          (StableCurveFramedTrait.special k).left ≅ pullback C.projection c.hom.left)
      (alpha : StableCurveFramedTrait.base k ⟶ P.J)
      (beta : Over.mk (𝟙 (Spec (.of k))) ⟶ P.J),
      IsHProjective (pullback.snd X.projection a.hom.left) ∧
      Flat (pullback.snd X.projection a.hom.left) ∧
      LocallyOfFinitePresentation (pullback.snd X.projection a.hom.left) ∧
      QuasiCompact (pullback.snd X.projection a.hom.left) ∧
      QuasiSeparated (pullback.snd X.projection a.hom.left) ∧
      e.hom ≫ pullback.snd C.projection c.hom.left =
        pullback.snd (pullback.snd X.projection a.hom.left)
          (StableCurveFramedTrait.special k).left ∧
      pullback.fst (pullback.snd X.projection a.hom.left)
          (StableCurveFramedTrait.special k).left ≫
          TenCanonicalHilbert.baseEmbedding (P.series X) a.hom.left ≫ phi.hom.left =
        e.hom ≫ TenCanonicalHilbert.baseEmbedding (P.series C) c.hom.left ≫
          tau.hom.left ≫ ProjectiveSpace.map (TenCanonicalHilbert.Coordinates g)
            (StableCurveFramedTrait.special k).left ∧
      Smooth (pullback.snd (pullback.snd X.projection a.hom.left)
        (StableCurveFramedTrait.generic k)) ∧
      P.hilbert.Classifies P.inclusion (P.series X) a.hom phi alpha ∧
      P.hilbert.Classifies P.inclusion (P.series C) c.hom tau beta ∧
      StableCurveFramedTrait.special k ≫ alpha = beta ∧
      (pullback.snd (pullback.snd X.projection a.hom.left)
        (StableCurveFramedTrait.generic k)).degree
          ((Scheme.Modules.tensorPullback
            (pullback.fst (pullback.snd X.projection a.hom.left)
                (StableCurveFramedTrait.generic k) ≫
              TenCanonicalHilbert.baseEmbedding (P.series X) a.hom.left ≫ phi.hom.left)).obj
            (ProjectiveSpace.twist (TenCanonicalHilbert.Coordinates g)
              (StableCurveFramedTrait.base k).left 1)) = 20 * ((g : ℤ) - 1) ∧
      (pullback.snd (pullback.snd X.projection a.hom.left)
        (StableCurveFramedTrait.generic k)).genus = g := by
  sorry

end AlgebraicGeometry
