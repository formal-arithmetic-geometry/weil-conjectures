/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.NormalCurveUniversalClosednessTest

/-! # Properness tested on local rings of normal finite-type curves

Source: Stacks Project, Limits, Tag 0GWX,
`lemma-essentially-finite-type-criterion-proper`, specialized to a field.
(blueprint: lem-sfb-properness-normal-curve-local-test).

The local ring is the structure-sheaf stalk and its fraction field is `FractionRing`.
Agreement on the generic spectrum is expressed on its canonical pullback with the
punctured open, as in `normal_curve_universal_closedness_test`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact morphism between schemes locally of finite type over a field is
proper if and only if every punctured normal finite-type curve diagram has a unique
lift from the spectrum of the local ring at the omitted closed point of dimension one.
Source: Stacks Project, Limits, Tag 0GWX, specialized to Spec k (fields are Nagata).
(blueprint: lem-sfb-properness-normal-curve-local-test).

Proof (the six steps of the DAG node):
1. Since f is over k, locallyOfFiniteType_of_comp
   (lemma-nagata-finite-type-to-separated-target) makes f locally of finite type;
   quasi-compactness makes it finite type (def-weil-finite-type-morphism).
   The field is Noetherian, so X and every test C are locally Noetherian by
   pqf-def-locnoeth and pqf-lem-locnoeth-lft.
2. If f is proper, the stalk R at c is Noetherian by its affine localization
   description (lem-weil-pbc-spec-local-ring-canonical-morphism and
   lem-weil-pbc-localization-noetherian). Normality and dimension one make it a DVR
   by lem-sc-normal-dim1-dvr, hence a valuation ring (def-sc-discrete-valuation-ring).
   Apply lemma-nagata-proper-separated-valuation-extension to the generic map
   induced by a and the local restriction of b. The lift is unique and is over k
   because its composite with f is over k.
3. Conversely, forget uniqueness. The existence clause is precisely the local test
   of lem-sfb-normal-curve-universal-closedness-test, so f is universally closed.
4. Set P = X times_Y X and let delta be the diagonal (def-pc-fibre-product).
   Its first projection is locally of finite type by lem-weil-pbc-lft-base-change;
   P is locally of finite type over k by lem-weil-pbc-proper-fp-permanence.
   Since the projection composed with delta is the identity, delta is locally of
   finite type by lemma-nagata-finite-type-to-separated-target. It is quasi-compact:
   intersections of affine opens in X are quasi-compact by
   lem-weil-pbc-locally-noetherian-quasi-separated. Products of affine opens over
   affine target opens cover P by affine opens (lem-weil-pbc-fibre-product-affine-spectra),
   and their inverse images under delta are these intersections. Basic opens pull
   back to basic opens (lem-weil-pbc-basic-open-pullback), and their quasi-compactness
   and finite basic-open covers follow from lem-weil-pbc-spec-localization-away-basic-open
   and lem-weil-pbc-affine-scheme-qcqs. Apply lem-pc-quasi-compact-local-on-target.
   Thus delta is finite type. It is a monomorphism by cancellation with a projection.
5. For a local curve test of delta, compose the map C to P with the two projections.
   These maps agree on U and have the same composite with f. Their local restrictions
   are two lifts for the original condition, so uniqueness makes them equal.
   The first gives the lift for delta by the fibre-product universal property
   (def-pc-fibre-product). Thus lem-sfb-normal-curve-universal-closedness-test makes
   delta universally closed.
6. A monomorphism is separated (lem-trf-scheme-monomorphism-separated), so delta
   is proper by its finite type and universal closedness (def-weil-proper-morphism).
   It is a closed immersion by lem-pc-proper-monomorphism-closed. Hence f is separated;
   combine this with steps 1 and 3 to obtain properness. No reduction of X or Y is used.
-/
theorem isProper_iff_normal_curve_local_test
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) [QuasiCompact f] (hf : f ≫ q = p) :
    IsProper f ↔
      ∀ (C : Scheme.{u}) (s : C ⟶ Spec (CommRingCat.of k))
        [IsIntegral C] [LocallyOfFiniteType s] [QuasiCompact s],
        (∀ z : C, IsDomain (C.presheaf.stalk z) ∧
          IsIntegrallyClosed (C.presheaf.stalk z)) →
        ∀ (c : C), IsClosed ({c} : Set C) → ringKrullDim (C.presheaf.stalk c) = 1 →
        ∀ (U : C.Opens), (U : Set C) = {c}ᶜ →
        ∀ (a : U.toScheme ⟶ X) (b : C ⟶ Y),
          a ≫ p = U.ι ≫ s → b ≫ q = s → a ≫ f = U.ι ≫ b →
          ∃! h : Spec (C.presheaf.stalk c) ⟶ X,
            h ≫ p = C.fromSpecStalk c ≫ s ∧
            h ≫ f = C.fromSpecStalk c ≫ b ∧
            pullback.snd U.ι
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
                    C.fromSpecStalk c) ≫
              Spec.map (CommRingCat.ofHom
                (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫ h =
            pullback.fst U.ι
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
                    C.fromSpecStalk c) ≫ a := by
  sorry

end AlgebraicGeometry
