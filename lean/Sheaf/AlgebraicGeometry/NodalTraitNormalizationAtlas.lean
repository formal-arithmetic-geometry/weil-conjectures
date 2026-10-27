/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.TraceFormula.StrictSemistableCurve
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback
import Sheaf.RingTheory.BinomialLaurentNormalForm
import Sheaf.AlgebraicGeometry.IntegralNormalGenericRecognition
import Sheaf.AlgebraicGeometry.SmoothTraitCurveLocalProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Sheaf.AlgebraicGeometry.EtaleSourceFibrePreparation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.BinomialGeometricFibres
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
/-! # Finite normalization atlas of a nodal curve over a trait
Source: Stacks Project, models.tex Tag 0CDD, curves.tex Tag 0CBY, and
more-morphisms.tex Tag 07TD; the finite-descent assembly in the DAG
(blueprint: lem-sfb-nodal-trait-normalization-atlas).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- The two-branch description on one chart, including the two specified axis restrictions
and compatibility of the isomorphism with the projection to the chart. The ring map is
characterized on every polynomial class, so it is the canonical map, not an arbitrary map.
Source: Stacks Project, models.tex Tag 0CDD and morphisms.tex Tag 0CDV, split-node calculation
(blueprint: lem-sfb-nodal-trait-normalization-atlas). -/
def NodalAtlasSplitBranchDescription {X U : Scheme.{u}} (p : U ⟶ X)
    (A : CommRingCat.{u}) (q : U ⟶ (StrictSemistableModel.nodal (0 : A)).scheme) : Prop :=
  ∃ b : strictNodalRing A 0 →+* (Polynomial A × Polynomial A),
    (∀ t : MvPolynomial (Fin 2) A,
      b (Ideal.Quotient.mk _ t) =
        (MvPolynomial.eval₂Hom Polynomial.C
            (fun i : Fin 2 => if i = 0 then Polynomial.X else 0) t,
          MvPolynomial.eval₂Hom Polynomial.C
            (fun i : Fin 2 => if i = 1 then Polynomial.X else 0) t)) ∧
    ∃ e : pullback (C := Scheme.{u}) X.fromReducedNormalization p ≅
        pullback (Spec.map (CommRingCat.ofHom b)) q,
      e.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom b)) q =
        pullback.snd X.fromReducedNormalization p
/-- A nodal projective flat finitely presented trait curve has a finite affine étale atlas
with the stated normalization descriptions, finite surjective normalization, nodal
projective flat finitely presented normalized family, and smooth normalized generic fibre.
Source: Stacks Project, models.tex Tag 0CDD, curves.tex Tag 0CBY, and
more-morphisms.tex Tag 07TD
(blueprint: lem-sfb-nodal-trait-normalization-atlas).
Proof:
1. A DVR is Noetherian. Finite type over a Noetherian base makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). The generic fibre is reduced by
   lem-trf-geometric-reducedness-algebraic-closure-test. Flatness on affines
   (lem-weil-pbc-flat-morphism-affine-criterion) and torsion-freeness
   (lem-trf-flat-module-torsionfree-domain) inject B into B[1/π], the reduced generic
   open by lem-weil-pbc-fibre-product-affine-spectra. Thus X is reduced. Nonclosed
   geometric-fibre points are component generic points and smooth by
   lem-trf-generic-fibre-points-smooth, so the closed-point condition covers every
   nonsmooth point.
2. Apply lem-sfb-dvr-nodal-etale-local-form at special-fibre points and restrict to
   affine neighbourhoods. Étaleness persists by
   lem-weil-pbc-etale-composition-cancellation; the affines are Noetherian by step 1.
3. Cover the smooth generic locus by affine smooth charts. At other generic points use
   lem-trf-nodal-family-etale-local-model, lem-weil-pbc-etale-fibre-discrete-separable-points,
   and lem-trf-nodal-model-etale-smooth-locus. The parameter is zero in the coefficient
   field, giving the split model over a finite separable extension. Restrict to affines.
4. Étale images are open (lem-weil-pbc-etale-morphism-open-map). Quasi-compactness gives
   a finite subcover. Its disjoint union is flat, surjective and quasi-compact: each
   affine chart is Noetherian. This is the fpqc cover used below.
5. Componentwise normalization is integral and surjective by
   lem-sfb-componentwise-normalization-generic-properties. Apply
   lem-sfb-componentwise-normalization-smooth-pullback twice, to the atlas and to the
   maps to the models. This requires no finite normalization or excellence assumption.
6. For zero-parameter models, lem-sfb-split-node-normalization-conductor supplies the
   finite two-axis normalization and smooth branches. Pull it back to each chart;
   lem-weil-pbc-etale-base-change-finite-limits makes its map to the branches étale.
7. For uv=π^n, n including zero, lem-sfb-binomial-laurent-normal-form proves normality
   over the normal DVR. The normal-domain clause of
   lem-sfb-split-node-normalization-conductor makes normalization the identity.
8. Normal schemes have identity normalization by lem-sfb-integral-normal-generic-recognition.
   Apply lem-sfb-smooth-normal-ascent on smooth generic charts and
   lem-sfb-smooth-trait-curve-local-properties on the relative smooth locus. The open
   case of lem-sfb-componentwise-normalization-smooth-pullback gives the restriction.
9. All pulled normalization maps are finite, either identities or tensor base changes
   of the finite split-node algebra (lem-weil-pbc-fibre-product-affine-spectra).
   Apply lem-sbc-finite-morphism-fpqc-descent to step 4. Surjectivity is from step 5.
10. Pulling the atlas back covers C by étale charts
    (lem-trf-etale-source-fibre-preparation, lem-weil-pbc-etale-base-change-finite-limits).
    Identity charts inherit the original nodal condition; separated branches are smooth
    affine lines. Use lem-trf-nodal-family-etale-source-locality and
    lem-sfb-scheme-nodal-etale-postcomposition to get flatness, local finite presentation,
    pure dimension one, and the nodal condition on C.
11. Identity-chart fibres are reduced by etale-proposition-etale-reduced. The other
    chart fibres are smooth, hence normal and reduced by lem-sfb-smooth-normal-ascent.
    Descent uses the faithfully flat local stalk maps
    (lem-weil-pbc-flat-local-hom-faithfully-flat), which are injective by
    lem-weil-pbc-faithfully-flat-universally-injective. Thus all geometric fibres are reduced.
12. Generic normalized charts are smooth: split branches are affine lines, and nonzero
    parameter charts become smooth hyperbolas by lem-sfb-binomial-geometric-fibres.
    Their coefficient-field extension is finite separable and étale by
    lem-weil-pbc-etale-fibre-discrete-separable-points and base change. Use
    lem-trf-smooth-composition, lem-weil-pbc-etale-smooth-zero-dimensional-fibres and
    lem-trf-etale-source-smoothness. Open normalization pullback identifies C_K with
    the componentwise normalization of X_K.
13. Finite normalization is projective in the bundle convention
    (lem-trf-finite-projective-bundle). Compose with f using
    lem-sfb-projective-bundle-composition. The affine trait has ample structure sheaf;
    lem-trf-projective-bundle-to-h-projective gives the required H-projectivity.
    Quasi-compactness follows from lem-sfb-projective-bundle-relative-ample and
    quasi-separatedness from the projective embedding. Together with step 10 this is
    finite presentation (def-sbc-locally-finite-presentation).
14. Surjectivity persists under geometric base change: the tensor product of two field
    extensions of the residue field is nonzero and has a prime. Use
    lem-weil-pbc-fibre-product-affine-spectra. Nonempty original fibres therefore give
    nonempty normalized fibres. No excellence or completeness was used. -/
theorem exists_nodal_trait_normalization_atlas
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : Irreducible π)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec R),
      Nonempty (pullback (C := Scheme.{u}) f g) ∧ IsReduced (pullback (C := Scheme.{u}) f g) ∧
        (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
        ∀ z : pullback (C := Scheme.{u}) f g,
        IsClosed ({z} : Set (pullback (C := Scheme.{u}) f g)) →
          ¬ ((NodalFiber.projection f Ω g).stalkMap z).hom.FormallySmooth →
          Nonempty (NodalFiber.completedLocalRing z ≃+* NodalFiber.powerSeriesQuotient Ω)) :
    IsNoetherian X ∧ IsReduced X ∧
    (∃ (m : ℕ) (U : Fin m → Scheme.{u}) (p : ∀ a, U a ⟶ X),
      (∀ a, IsAffine (U a) ∧ Etale (p a)) ∧
      (∀ x : X, ∃ (a : Fin m) (z : U a), p a z = x) ∧
      ∀ a : Fin m,
        ((∃ z : U a, f (p a z) = IsLocalRing.closedPoint R) →
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (φ : R →+* A) (t : A),
            Function.Injective φ ∧ IsLocalHom φ ∧
            Etale (Spec.map (CommRingCat.ofHom φ)) ∧ Irreducible t ∧
            ((∃ q : U a ⟶ (StrictSemistableModel.nodal (0 : A)).scheme,
              Etale q ∧ p a ≫ f = q ≫ (StrictSemistableModel.nodal (0 : A)).baseMap ≫
                Spec.map (CommRingCat.ofHom φ) ∧ NodalAtlasSplitBranchDescription (p a) A q) ∨
            ∃ (n : ℕ) (q : U a ⟶ (StrictSemistableModel.nodal (t ^ n)).scheme),
              Etale q ∧ p a ≫ f = q ≫ (StrictSemistableModel.nodal (t ^ n)).baseMap ≫
                Spec.map (CommRingCat.ofHom φ) ∧ IsIso (pullback.snd X.fromReducedNormalization
                  (p a)))) ∧
        ((¬ ∃ z : U a, f (p a z) = IsLocalRing.closedPoint R) →
          ∃ r : U a ⟶ Spec (.of K),
            p a ≫ f = r ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
            ((Smooth r ∧ IsIso (pullback.snd X.fromReducedNormalization (p a))) ∨
            ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
              (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
              (q : U a ⟶ (StrictSemistableModel.nodal (0 : CommRingCat.of L)).scheme),
              Etale q ∧ r = q ≫ (StrictSemistableModel.nodal (0 : CommRingCat.of L)).baseMap ≫
                Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
              NodalAtlasSplitBranchDescription (p a) (.of L) q))) ∧
    IsFinite X.fromReducedNormalization ∧ Surjective X.fromReducedNormalization ∧
    IsHProjective (X.fromReducedNormalization ≫ f) ∧
    Flat (X.fromReducedNormalization ≫ f) ∧
    LocallyOfFinitePresentation (X.fromReducedNormalization ≫ f) ∧
    QuasiCompact (X.fromReducedNormalization ≫ f) ∧
    QuasiSeparated (X.fromReducedNormalization ≫ f) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec R),
      Nonempty (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g) ∧
      IsReduced (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g) ∧
      (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g).IsPureDimension 1 ∧
      ∀ z : pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g,
        IsClosed ({z} : Set (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g)) →
        ¬ RingHom.FormallySmooth
          ((NodalFiber.projection (X.fromReducedNormalization ≫ f) Ω g).stalkMap z).hom →
        Nonempty (NodalFiber.completedLocalRing z ≃+* NodalFiber.powerSeriesQuotient Ω)) ∧
    Smooth (pullback.snd (X.fromReducedNormalization ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
    IsIso (pullback.snd X.fromReducedNormalization f.smoothLocus.ι) ∧
    (∃ e : pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
        (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).reducedNormalization,
      e.hom ≫
        (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).fromReducedNormalization ≫
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        pullback.fst (X.fromReducedNormalization ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ X.fromReducedNormalization ∧
      e.hom ≫
        (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).fromReducedNormalization ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        pullback.snd (X.fromReducedNormalization ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  sorry
end AlgebraicGeometry
