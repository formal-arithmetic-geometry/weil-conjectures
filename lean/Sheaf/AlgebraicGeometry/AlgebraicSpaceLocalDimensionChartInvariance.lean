/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.RingTheory.Etale.LocalDimension
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Local dimension computed by étale scheme charts

Source: Stacks Project, Properties of Spaces, Tags 0BAM and 04NA
(blueprint: lem-sfb-space-local-dimension-chart-invariance).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point admits an étale scheme chart. Any two such charts give the same stalk
Krull dimension, hence a unique value in `ℕ∞`, agreeing with scheme stalk dimension
under every scheme representation. No finiteness or quasi-separatedness is assumed.
Source: Stacks Project, Properties of Spaces, Tags 0BAM and 04NA
(blueprint: lem-sfb-space-local-dimension-chart-invariance).

Proof:
1. Choose the surjective étale atlas from `def-trf-algebraic-space`; the point-surjectivity
   criterion of `lem-a1-space-point-open-calculus` lifts the given point to the atlas.
2. For two charts form their sheaf fibre product, a scheme by representability. Both
   projections are étale by base change (`lem-trf-space-fibre-products-etale-covers`).
   The common-field criterion and `lem-a1-space-fibre-product-point` provide a point
   of this scheme above the two given points, even for non-surjective charts.
3. Around this point and each image choose affine opens on which the projection is an
   étale ring map (`def-weil-etale-morphism`). Identify stalks with prime localizations
   (`lem-weil-pbc-affine-open-stalk-localization`). Apply
   `lem-sc-etale-local-dimension` to each projection. Ring isomorphisms preserve prime
   chains, so both original stalk dimensions equal the dimension at the common point.
4. A scheme stalk is a nonzero local ring, hence its dimension is nonnegative. Its
   dimension therefore comes from `ℕ∞`, including infinity. A lifted chart gives a value;
   step 3 makes it independent of all chart choices and forces uniqueness
   (`def-weil-pbc-krull-dimension-ring`).
5. Under a scheme representation, the identity of that scheme is an étale chart.
   Comparing with it gives the stated equality with the scheme stalk dimension. -/
theorem etaleChart_localDimension {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Point X.obj.obj) :
    (∃ (W : Over S) (a : yoneda.obj W ⟶ X.obj.obj),
      IsEtale a ∧ ∃ w : W.left, schemePointMap a w = x) ∧
    (∀ (W₁ W₂ : Over S) (a₁ : yoneda.obj W₁ ⟶ X.obj.obj)
      (a₂ : yoneda.obj W₂ ⟶ X.obj.obj),
      IsEtale a₁ → IsEtale a₂ → ∀ (w₁ : W₁.left) (w₂ : W₂.left),
      schemePointMap a₁ w₁ = x → schemePointMap a₂ w₂ = x →
      ringKrullDim (W₁.left.presheaf.stalk w₁) =
        ringKrullDim (W₂.left.presheaf.stalk w₂)) ∧
    ∃! d : ℕ∞,
      (∀ (W : Over S) (a : yoneda.obj W ⟶ X.obj.obj), IsEtale a →
        ∀ w : W.left, schemePointMap a w = x →
          ringKrullDim (W.left.presheaf.stalk w) = (d : WithBot ℕ∞)) ∧
      (∀ (T : Over S) (e : yoneda.obj T ≅ X.obj.obj) (t : T.left),
        schemePointMap e.hom t = x →
          (d : WithBot ℕ∞) = ringKrullDim (T.left.presheaf.stalk t)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
