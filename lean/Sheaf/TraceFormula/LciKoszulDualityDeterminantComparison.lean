/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.TraceFormula.LciKoszulDualityData
public import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
import WeilConjectures.RingTheory.KoszulDualComplex
import Sheaf.AlgebraicGeometry.PolynomialDualityPresentationData
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.TraceFormula.AffineTwoTermDeterminant
import Sheaf.Algebra.Homology.DerivedBimoduleTensorHom
import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
import Sheaf.RingTheory.NaiveCotangentComparison
import Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.KoszulDifferential
import WeilConjectures.RingTheory.KoszulTensorConeCoordinates
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Normalized Koszul duality and the cotangent determinant

Source: Stacks, duality.tex, Tags 0BQZ and 0BV2; dualizing.tex, Tags 0BZI and 0BZJ;
more-algebra.tex, Tags 0FJI and 0FJM
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Algebra.CotangentResolution AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.LciKoszulDuality

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

attribute [local instance] schemeDerived imageRingDerived imageRingInjectives

/-- Ordinary pullback and open restriction are the unique left adjoints of the same
actual direct image. Source: Stacks 0095, 01CU
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def openTensorIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).leftAdjointUniq
    (Scheme.Modules.restrictAdjunction j)

/-- The intrinsic cotangent square of this chart, including its specified base-ring map.
Source: Stacks 08QQ (blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.square {C : Coherence.{u}} (D : CotangentPresentation.System C)
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  D.square f (T.chart.i ≫ T.chart.base) T.chart.U.ι (𝟙 S)
    (by simpa only [RelativeDualityPolynomialChart.base, Category.comp_id,
      Category.assoc] using T.chart.factor.symm)

/-- Exactness of the actual closed-immersion direct image, used to identify its
single-degree objects by the derived-functor unit. This is conclusion data, not a hypothesis.
Source: Stacks 0BQZ (blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
structure Chart.ImageExact {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) where
  limits : PreservesFiniteLimits
    (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace T.chart.i))
  colimits : PreservesFiniteColimits
    (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace T.chart.i))

/-- The shifted Hom model is the shift of the unshifted Hom, with the derived
functor's standard shift comparison. Source: Stacks 0BV2
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.modelShift {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i) :
    T.chart.model h.additive ≅ (T.unshiftedModel h)⟦(T.chart.n : ℤ)⟧ := by
  letI := h.additive
  exact ((polynomialChartCoinduction T.chart.i).rightDerivedFunctor.commShiftIso
    (T.chart.n : ℤ)).app ((DerivedCategory.singleFunctor _ 0).obj T.omega)

/-- The target shift, using n-c=d and the exact direct-image unit on single complexes.
Source: Stacks 0BQZ, 0BV2
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.targetShift {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : T.ImageExact) : T.unshiftedTarget⟦(T.chart.n : ℤ)⟧ ≅ T.target := by
  letI := h.limits
  letI := h.colimits
  exact ((DerivedCategory.singleFunctors _).shiftIso (T.chart.n : ℤ) (-(d : ℤ))
      (T.c : ℤ) (by have hn := T.dimension; omega)).app T.imageLine ≪≫
    (((DerivedCategory.singleFunctors _).shiftIso (d : ℤ) (-(d : ℤ)) 0
      (add_neg_cancel _)).app T.imageLine).symm ≪≫
    (shiftFunctor _ (d : ℤ)).mapIso
      (((Functor.singleFunctorCompRightDerivedFunctorIso
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace T.chart.i)))).app T.line).symm ≪≫
    (Functor.commShiftIso
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace T.chart.i)).rightDerivedFunctor
        (d : ℤ)).symm.app _

/-- The comparison rho[n], retaining the quotient-algebra action and all shift signs.
Source: Stacks 0BQZ, 0BV2
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.shifted {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i) (hI : T.ImageExact)
    (ρ : T.unshiftedModel h ≅ T.unshiftedTarget) :
    T.chart.model h.additive ≅ T.target :=
  T.modelShift h ≪≫ (shiftFunctor _ (T.chart.n : ℤ)).mapIso ρ ≪≫ T.targetShift hI

/-- One canonical conormal comparison, expressed in the existing two-term determinant
model. Its term maps fix the model isomorphism, and its derived map is lambda from the
recorded intrinsic cotangent system, not an arbitrary isomorphism of the same objects.
Source: Stacks 08SL, 08QQ
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
structure Chart.CotangentData {C : Coherence.{u}} (D : CotangentPresentation.System C)
    (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison C)
    (E : CotangentPresentation.LciIdentifications D F κ)
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) where
  ambient_free : SheafOfModules.IsFiniteLocallyFreeOfRank
    (CotangentPresentation.ambientDifferentials T.chart.i T.chart.base) T.chart.n
  model : (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
      ambient_free).complex ≅
    (E.identification T.chart.i T.chart.base T.presentation).model.complex
  negative : model.hom.f (-1) ≫
      (E.identification T.chart.i T.chart.base T.presentation).model.negative.hom =
    (HomologicalComplex.doubleXIso₀
      (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
        ambient_free).differential (by decide)).hom
  zero : model.hom.f 0 ≫
      (E.identification T.chart.i T.chart.base T.presentation).model.zero.hom =
    (HomologicalComplex.doubleXIso₁
      (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
        ambient_free).differential (by decide) (by decide)).hom
  lambda : DerivedCategory.Q.obj
      (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
        ambient_free).complex ≅
    (derivedPullback T.chart.U.ι).obj (CotangentPresentation.cotangent (D.model f))
  lambda_eq : lambda.hom ≫ CotangentPresentation.derivedChange D (T.square D) =
    DerivedCategory.Q.map model.hom ≫
      (E.identification T.chart.i T.chart.base T.presentation).iso.hom

/-- The determinant restriction dictated by lambda, with no choice of a trivialization.
Its comparison between two charts is precisely det(lambda_j inverse lambda_i).
Source: Stacks 0FJI, 0FJM, 08SL
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.determinantIso {C : Coherence.{u}} {D : CotangentPresentation.System C}
    {F : CotangentPresentation.AffineIdentifications D} {κ : Naive.Comparison C}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (N : T.CotangentData D F κ E) (δ : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) :
    (Scheme.Modules.restrictFunctor T.chart.U.ι).obj
      (twoTermDeterminantValue (δ.functor X) (CotangentPresentation.cotangent (D.model f)) hL) ≅
        T.line :=
  (openTensorIso T.chart.U.ι).symm.app _ ≪≫
    δ.pullbackIso T.chart.U.ι _ hL ≪≫
    twoTermDeterminantIso (δ.functor T.chart.U.toScheme)
      (δ.pullback_mem T.chart.U.ι _ hL)
      (δ.model_mem (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
        N.ambient_free)) N.lambda.symm ≪≫
    δ.modelIso (T.twoTerm (E.identification T.chart.i T.chart.base T.presentation).model
      N.ambient_free)

/-- The intrinsic determinant object, with its relative dimension shift.
Source: Stacks 0FJX, 0BV2
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def determinantObject {C : Coherence.{u}} (D : CotangentPresentation.System C)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (δ : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) :
    schemeDerivedCategory.{u, w} X :=
  ((DerivedCategory.singleFunctor.{w} X.Modules 0).obj
    (twoTermDeterminantValue (δ.functor X) (CotangentPresentation.cotangent (D.model f))
      hL))⟦(d : ℤ)⟧

/-- Apply the determinant restriction to shifted single complexes, using exact restriction.
Source: Stacks 0FJX (blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def Chart.determinantShift {C : Coherence.{u}} {D : CotangentPresentation.System C}
    {F : CotangentPresentation.AffineIdentifications D} {κ : Naive.Comparison C}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (N : T.CotangentData D F κ E) (δ : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) :
    (polynomialOpenRestriction T.chart.U.ι).obj (determinantObject D f d δ hL) ≅
      ((DerivedCategory.singleFunctor _ 0).obj T.line)⟦(d : ℤ)⟧ :=
  ((Functor.commShiftIso
    (Scheme.Modules.restrictFunctor T.chart.U.ι).mapDerivedCategory (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (d : ℤ)).mapIso
      ((Functor.mapDerivedCategorySingleFunctor
        (Scheme.Modules.restrictFunctor T.chart.U.ι) 0).app _) ≪≫
    (shiftFunctor _ (d : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (T.determinantIso N δ hL))

/-- Exactly the normalized affine and principal-open comparisons required by the recorded
polynomial-chart theorem. In particular refinement is the independent coinduction boundary
for t-a and contraction of d(t-a); comparison is not defined freely from determinant maps.
Source: Stacks 0BZI, 0BZJ
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
def IsNormalizedAtlas {X S : Scheme.{u}} {f : X ⟶ S} {K : schemeDerivedCategory X}
    (atlas : PolynomialDualityChartAtlas f K) : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S)
    [IsOpenImmersion jA] [IsOpenImmersion jR],
    jA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ jR →
    ∃ (M : DerivedCategory (ModuleCat.{u} A))
      (e : (polynomialOpenRestriction jA).obj K ≅ (polynomialAffineTilde A).obj M)
      (F : PolynomialDualityPresentationSystem R A (algebraMap R A) M),
      IsPolynomialAffineAtlasCompatible atlas R A jA jR M e F ∧
      IsPolynomialLocalizedAffineAtlasCompatible atlas R A jA jR M e F

/-- All comparisons in the assertion, sharing one atlas on the intrinsic determinant.
The last equation identifies the independently normalized Hom comparisons with the
specified determinant maps. The atlas's restriction square and affine compatibility
then state the claimed restriction, elementary refinement, combined refinement and
composition equalities for these same rho maps.
Source: Stacks 0BQZ, 0BV2, 0BZI, 0BZJ, 0FJI
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison). -/
structure ComparisonData {C : Coherence.{u}} (D : CotangentPresentation.System C)
    (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison C)
    (E : CotangentPresentation.LciIdentifications D F κ)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (δ : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) where
  atlas : PolynomialDualityChartAtlas f (determinantObject D f d δ hL)
  normalized_atlas : IsNormalizedAtlas atlas
  cotangent : ∀ T : Chart f d, T.CotangentData D F κ E
  image_exact : ∀ T : Chart f d, T.ImageExact
  rho : ∀ T : Chart f d, T.unshiftedModel (atlas.exactData T.chart) ≅ T.unshiftedTarget
  normalized : ∀ T : Chart f d, T.IsNormalized (atlas.exactData T.chart) (rho T)
  determinant : ∀ T : Chart f d,
    (atlas.identification T.chart).hom ≫
      (T.shifted (atlas.exactData T.chart) (image_exact T) (rho T)).hom =
    T.image.map (T.determinantShift (cotangent T) δ hL).hom

/-- Normalized Koszul duality is the intrinsic cotangent determinant, unconditionally
on polynomial lci charts. Only the final implication assumes the hypotheses ensuring
existence of a normalized relative dualizing object. The determinant datum is the
canonical one of the dependency: its exterior-model and pullback comparisons are the
kernel-first good-diagram maps, so the chart transitions are det(lambda_j inverse lambda_i)
with their signs, not up to a free rescaling of each model.

Source: Stacks duality.tex, Tags 0BQZ and 0BV2; dualizing.tex, Tags 0BZI and 0BZJ;
more-algebra.tex, Tags 0FJI and 0FJM
(blueprint: lem-trf-lci-koszul-duality-determinant-comparison).

Proof:
1. On an affine ambient with regular generators g use the finite free Koszul resolution
and its signed dual. Its only cohomology is in degree c. The quotient-linear top map
pairs with the ordered conormal wedge as (-1)^(c(c-1)/2) times the functional's value.
Tensor with the ambient differential line. All coefficients and all generators occur
in the normalization formula, so the result is independent of the ambient frame and
the generators. Quotient-augmented Koszul roofs identify the same top Ext map.
2. Restriction of internal Hom and localization of Koszul duality glue the top maps.
Keep the quotient action by coinduction, whose action is precomposition with multiplication
and whose counit is evaluation at one. Truncate the coinduced complex in degree c;
the inclusion and projection to H^c give the canonical quasi-isomorphism roof.
Closed-immersion direct image is exact, so the target is the actual pushed-forward line.
3. The conormal differential and its canonical cotangent comparison give the displayed
local two-term models. The lci cover proves the intrinsic cotangent object is two-term
perfect. Apply the determinant functor constructed by kernel-normalized good diagrams.
4. For Q=P[t] and h=t-a the monic equation is regular. The enlarged Koszul resolution
is the ordered tensor with K(h); the conormal complex is the old complex plus
[O h -> O d(h)], with differential 1. The projection represents the specified cotangent
comparison. Derived coinduction transitivity identifies the refinement with the boundary
of multiplication by h, followed by evaluation dual(h) tensor d(h) -> 1.
5. On raw top Hom classes, moving the h contraction past the old shift gives (-1)^n.
The ratio of normalized Koszul signs is (-1)^c. Hence the appended-generator determinant
comparison has sign (-1)^(n+c). The kernel-first determinant formula has the same sign:
move h past c conormal generators and d(h) past n differential generators, and evaluate.
Thus the comparison is exactly determinant(lambda_j inverse lambda_i)[d].
6. Different lifts differ by an elementary triangular conormal change and a chain
homotopy; they induce the same derived map. Iterate the elementary comparison, including
the identity refinement. Evaluation counits associate, determinant is a functor, and
interchanging equations and differentials gives the matching wedge and total-Hom signs.
A common combined-coordinate refinement therefore gives all presentation comparisons
and their composition laws. Principal localization uses the same boundary for ht-1;
its coefficient contraction includes h inverse. These are precisely the normalized
affine presentation systems and restriction squares in the conclusion's atlas.
7. If the base is locally Noetherian and f is separated, flat and locally of finite
presentation, the recorded polynomial-chart theorem supplies the normalized relative
dualizing object. Its chart atlas and the preceding determinant atlas have the same
normalized comparisons. The local isomorphisms glue, and their chart equations are
exactly the last equation below. Full faithfulness on shifted lines makes the glued
map unique. No dualizing object is used in steps 1--6. The empty chart, zero ring,
empty regular sequence and degree-zero volume are covered by these same formulas. -/
theorem exists_lciKoszulDualityDeterminantComparison
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (C : Coherence.{u}) (κ : Naive.Comparison C) (D : CotangentPresentation.System C)
    (F : CotangentPresentation.AffineIdentifications D)
    (E : CotangentPresentation.LciIdentifications D F κ)
    (_hD : CotangentPresentation.Properties D F κ E)
    (δ : TwoTermPerfectDeterminantData.{u, w}) (_hδ : δ.IsCanonical)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (_cover : ∀ x : X, ∃ T : Chart f d, x ∈ T.chart.U) :
    ∃ (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f)))
      (B : ComparisonData D F κ E f d δ hL),
      ∀ [_hS : IsLocallyNoetherian S] [_hsep : IsSeparated f] [_hflat : Flat f]
        [_hlfp : LocallyOfFinitePresentation f],
      ∀ (K : schemeDerivedCategory X)
        (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
          (derivedPullback (pullback.fst f f)).obj K)
        (atlas : PolynomialDualityChartAtlas f K),
        IsCoherentRelativeDualizingPair f K ξ → IsNormalizedAtlas atlas →
        ∃ β : K ≅ determinantObject D f d δ hL,
          ∀ T : Chart f d,
            (atlas.identification T.chart).hom ≫
              (T.shifted (atlas.exactData T.chart) (B.image_exact T) (B.rho T)).hom =
            T.image.map ((polynomialOpenRestriction T.chart.U.ι).map β.hom) ≫
              T.image.map (T.determinantShift (B.cotangent T) δ hL).hom := by
  sorry

end AlgebraicGeometry.LciKoszulDuality
