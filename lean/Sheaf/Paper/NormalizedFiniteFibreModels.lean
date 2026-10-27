/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilRestrictionData
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence

/-! # The normalized finite sf fibre in the realization presentation

Source: BS 6.8.14(2), 6.8.15; Stacks 099N(5); blueprint
`thm-zl-real-mixed-by-curves`, paragraph 7 and the local-operator convention
(blueprint: def-zl-normalized-finite-fibre-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
open AlgebraicallyClosedCoefficients (Coefficient)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The two recorded coefficient transports coincide: both are restriction along
 the unique completed-ring isomorphism fixed on every finite quotient generator.
Source: Stacks 099N(5) (blueprint: def-zl-normalized-finite-fibre-models).
Proof: the finite ring comparisons send every quotient representative to its size lift.
Their completed maps agree by the limit projection equations. Restriction along
these equal maps, and its exact derived localization, therefore agree. -/
theorem coefficientTransport_eq (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    (purCoefficientModel l E X).functor = IntegralCompletedComparison.derived l E X := by
  sorry

/-- The inverse coefficient representative has the same bounded complete predicate.
Source: BS 6.8.11(3), Stacks 099N
(blueprint: def-zl-normalized-finite-fibre-models).
Proof: apply the bounded-predicate comparison and the counit of purCoefficientModel.
Finite type over the field supplies the Noetherian and finite-dimensional bounds;
prime-to-characteristic invertibility supplies the stalk and global unit hypotheses. -/
theorem finiteIntegralModel_mem (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :
    PbcIsBoundedConstructibleComplete X.scheme (pbcStageDatum.{u} l Ω E)
      ((purCoefficientModel l (Coefficient.{u} l Ω E) X.scheme).inverse.obj K.obj) := by
  sorry

/-- The integral representative is the inverse of the fixed coefficient equivalence.
Source: BS 6.8.11(3) (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteIntegralModel (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :
    pbcIntegralStage.{u, u + 1} l Ω X.scheme E :=
  ⟨(purCoefficientModel l (Coefficient.{u} l Ω E) X.scheme).inverse.obj K.obj.obj,
    finiteIntegralModel_mem D l Ω X E K.obj⟩

/-- The fixed coefficient counit inside the full integral constructible category.
Source: BS 6.8.11(3) (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteModelCounit (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :
    (adicCalculusIntegralModel l Ω X.scheme E ((R.models X).model_mem E)).obj
      (finiteIntegralModel D l Ω X E K) ≅ K.obj :=
  (sfIntegralConstructible l (Coefficient.{u} l Ω E) X.scheme).isoMk
    ((purCoefficientModel l (Coefficient.{u} l Ω E) X.scheme).counitIso.app K.obj.obj)

/-- Rationalization of the integral coefficient counit, with its actual object map.
Source: BS 6.8.14 (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteRationalModelCounit (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :
    (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X.scheme).obj
      ((adicCalculusIntegralModel l Ω X.scheme E ((R.models X).model_mem E)).obj
        (finiteIntegralModel D l Ω X E K)) ≅ K :=
  (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X.scheme).mapIso
    (finiteModelCounit D l Ω R X E K)

/-- Apply the actual finite-stage inclusion to an isomorphism, retaining the
category's recorded scalar-localization instance.
Source: BS 6.8.14 (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteCommonIso (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω)
    {K L : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E} (e : K ≅ L) :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X.scheme) E).mapIso e

/-- The common-stage image of the fixed rational coefficient counit.
Source: BS 6.8.14 (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteCommonModelCounit (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :=
  finiteCommonIso D l Ω X E (finiteRationalModelCounit D l Ω R X E K)

/-- The stage identification is the recorded integral comparison followed by its
coefficient-model counit; it does not use a Weil structure or a classical fibre.
Source: BS 6.8.14 (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteStageIso (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme) :=
  ((R.models X).comparison_integral E).app (finiteIntegralModel D l Ω X E K) ≪≫
    finiteCommonModelCounit D l Ω R X E K

/-- At a geometric point the normalized completed comparison has a unique component
on a bounded constructible integral representative. This universal characterization
makes choosing its component independent of every comparison witness.
Source: BS 6.8.14(2), Stacks 099N(5)
(blueprint: def-zl-normalized-finite-fibre-models).
Proof: existence follows from the integral completed-pullback comparison. Its
finite-normalization clause fixes every finite comparison on tensor-unit generators,
and its good-representative projection clause therefore fixes the reductions of gamma.
At the algebraically closed point the reductions of both pullbacks have bounded finite
cohomology over the finite quotient ring. Their derived Hom groups at each positive
level are finite. The inverse Hom towers are consequently Mittag-Leffler, so their
lim1 groups vanish. Derived completeness then identifies Hom with the inverse limit
of these finite-level Hom groups. Hence two such components with the same normalized
projections agree. Iso.ext gives uniqueness of the isomorphism as well as its arrow.
This argument uses only completed point sections, without a Weil structure. -/
theorem finitePointComparison_existsUnique (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :
    let F := Coefficient.{u} l Ω E
    let J := finiteIntegralModel D l Ω X E K
    ∃! e : (IntegralCompletedComparison.integral l F x).obj J.obj ≅
        (IntegralCompletedComparison.completed l F x).obj J.obj,
      ∀ (C : IntegralCompletedComparison.Comparison l F x)
        (h : IntegralCompletedComparison.Complete l F J.obj), C.gamma J.obj h = e := by
  sorry

/-- Integral point pullback is the normalized strict-tower comparison. Its gamma
is determined on every good representative by both Roos projection coordinates and
finite tensor-unit generators, as retained in IntegralCompletedComparison.Comparison.
Source: Stacks 099N(5) (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteIntegralPointIso (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :
    (integralDerivedPullback l (Coefficient.{u} l Ω E) x).obj K.obj.obj ≅
      (purCoefficientModel l (Coefficient.{u} l Ω E) (Spec (.of D.k))).functor.obj
        ((pbcActualCompletedPull x (pbcStageDatum.{u} l Ω E)).obj
          (finiteIntegralModel D l Ω X E K).obj) :=
  let F := Coefficient.{u} l Ω E
  let Φ := purCoefficientModel l F X.scheme
  let J := finiteIntegralModel D l Ω X E K
  (integralDerivedPullback l F x).mapIso (Φ.counitIso.app K.obj.obj).symm ≪≫
    eqToIso (congrArg (fun G ↦ (integralDerivedPullback l F x).obj (G.obj J.obj))
      (coefficientTransport_eq l F X.scheme)) ≪≫
    (finitePointComparison_existsUnique D l Ω X E K x).exists.choose ≪≫
    eqToIso (congrArg (fun G ↦ G.obj
      ((pbcActualCompletedPull x (pbcStageDatum.{u} l Ω E)).obj J.obj))
        (coefficientTransport_eq l F (Spec (.of D.k))).symm)

/-- The sf finite point fibre normalized to H0 of the completed point sections.
Source: blueprint point convention, BS 6.8.14
(blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteSfPointIso (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :=
  let F := Coefficient.{u} l Ω E
  let P := (rationalDerivedPullback l F x).obj K
  LisseRealization.fibreNormalization D l (Fact.out : l ≠ D.p) F P ≪≫
    ((pointModuleRationalization l F).mapDerivedCategoryHomologyFunctorIso 0).symm.app
      ((pointCompletedDerivedSections D.k l F).obj P.obj.obj) ≪≫
    (pointModuleRationalization l F).mapIso
      (((pointCompletedSections D.k l F).mapDerivedCategoryHomologyFunctorIso 0).symm.app
        P.obj.obj) ≪≫
    (pointModuleRationalization l F).mapIso
      ((pointCompletedSections D.k l F).mapIso
        ((DerivedCategory.homologyFunctor _ 0).mapIso
          ((sfIntegralConstructible l F (Spec (.of D.k))).ι.mapIso
            (CompletedStalk.rationalUnderlyingPullback l F x K))))

/-- Coefficient tensor composition in the actual two coefficient universes, using
 the composite adjunction and the identity-on-elements restriction comparison.
Source: BS 6.8.14 (blueprint: def-zl-normalized-finite-fibre-models). -/
def finiteTensorComp (E : Padic.FiniteCoefficientFields l Ω) :
    ModuleCat.extendScalars.{u, u + 1, u + 1}
      ((sfAdicCoefficientEmbedding.{u} l Ω E).comp
        (algebraMap (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
          (Coefficient.{u} l Ω E))) ≅
    pointModuleRationalization l (Coefficient.{u} l Ω E) ⋙
      ModuleCat.extendScalars.{u, u + 1, u + 1} (sfAdicCoefficientEmbedding.{u} l Ω E) :=
  let f := algebraMap (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
    (Coefficient.{u} l Ω E)
  let g := sfAdicCoefficientEmbedding.{u} l Ω E
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u + 1} g))
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u + 1} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl).symm

end WeilConjectures.ZlFrontier
