module

public import Sheaf.Paper.PurityTateDatum
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-!
# The specified Frobenius comparison on strict integral systems

Source: the scheme-Frobenius construction of `def-pur-tate-datum` and Returned
Step 11 of the constituent-compatibility assembly
(blueprint: def-pur-kappa-coefficient-stage-comparisons).

The finite ordinary map is the relative-Frobenius adjunction mate. Its maps on
whole strict towers, and its completed descent, are determined by their displayed
normalizations. No comparison is a parameter of these constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary relative-Frobenius adjunction mate used to define the published κ.
Source: the displayed factorization in `def-pur-scheme-geometric-frobenius`
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaOrdinaryFor (P : PurityFiniteSetting.{u}) (A : Type u) [CommRing A] [Finite A]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingPullback A (P.frobeniusSchemeMap T₀) ≅
      proEtaleConstantRingPullback A (P.frobeniusGaloisMap T₀) :=
  eqToIso (congrArg (proEtaleConstantRingPullback A)
      (P.schemeGeometricFrobenius_factorization T₀).2.2) ≪≫
    (absoluteFrobenius_proEtale_trivialization_pullback
      P.field.p P.field.prime A).choose_spec.2.choose
        (P.frobeniusAbsoluteMap T₀) (P.frobeniusGaloisMap T₀) ≪≫
    Functor.isoWhiskerLeft
      (proEtaleConstantRingPullback A (P.frobeniusGaloisMap T₀))
      ((absoluteFrobenius_proEtale_trivialization_pullback
        P.field.p P.field.prime A).choose_spec.2.choose_spec.2.choose
          (P.frobeniusFiber T₀).left
          ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
            (P.field.model_characteristic
              (pullback.fst T₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫
                  T₀.hom))⟩ P.field.a) ≪≫
    Functor.rightUnitor _

/-- The finite coefficient ring has its canonical finiteness structure.
Source: positive-level quotient convention
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
instance kappaRingFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The ordinary comparison at the fixed finite stage.
Source: specified κ factorization (blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaOrdinary (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) := P.kappaOrdinaryFor P.Ring T₀

/-- The standard localization already fixed in `proEtaleDerivedCategory`.
The specialized instance fixes the native coefficient size before the general
integral-Hom instance is tried; both use `HasDerivedCategory.standard`.
Source: the pro-etale derived-category convention
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
instance (priority := 2000) kappaFiniteDerivedCategory
    (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _

/-- Exact descent of the specified finite-ring comparison.
Source: relative-Frobenius factorization
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaFiniteFor (P : PurityFiniteSetting.{u}) (A : Type u) [CommRing A] [Finite A]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :=
  Functor.mapDerivedCategoryNatIso (P.kappaOrdinaryFor A T₀)

/-- Exact descent of the ordinary map gives the recorded finite comparison itself.
Source: the specified κ factorization (blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: expand the ordinary factorization. Exact descent preserves its composition,
whiskering, equality transport and right unitor. The resulting four factors are the
definition of `schemeGeometricFrobeniusComparison`, in the same order. -/
theorem kappaOrdinary_derived (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    Functor.mapDerivedCategoryNatIso (P.kappaOrdinary T₀) =
      P.schemeGeometricFrobeniusComparison T₀ := by
  sorry

variable (P : PurityFiniteSetting.{u}) (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]

/-- Finiteness of every actual positive quotient used in the strict system.
Source: finite coefficient convention
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
instance kappaQuotientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing P.coefficients.l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))

/-- The actual level map, including both unit-normalized presentation changes.
Source: Returned Step 11, strict-system construction
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaStrictLevel
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) (n : ℕ) :
    integralOperationsPullbackLevel P.coefficients.l E
        (P.frobeniusSchemeMap T₀) n ≅
      integralOperationsPullbackLevel P.coefficients.l E
        (P.frobeniusGaloisMap T₀) n :=
  Functor.isoWhiskerLeft
    (unrestrictedIntegralFiniteComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left n)
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (integralFinitePullbackModel P.coefficients.l E
            (P.frobeniusSchemeMap T₀) n ≪≫
          P.kappaOrdinaryFor (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)) T₀ ≪≫
          (integralFinitePullbackModel P.coefficients.l E
            (P.frobeniusGaloisMap T₀) n).symm) (.up ℤ))
      (integralOperationsRestrict P.coefficients.l E
        (P.frobeniusFiber T₀).left n))

/-- The level maps determine one isomorphism of whole strict cochain systems.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: on every section, the relative-Frobenius restriction and its inverse
commute with every quotient transition, since the coefficient factor is unchanged.
Naturality gives compatibility with differentials and maps of input complexes.
The normalized finite presentation maps preserve these transition equations.
Thus the component maps and their inverses form natural maps of towers. Their
inverse identities hold at every level. Evaluation on all levels is jointly
faithful for maps of strict systems, which gives the asserted uniqueness before
any derived inverse limit is applied. -/
theorem kappaStrict_existsUnique
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    ∃! κ : integralOperationsPullbackTowerFunctor P.coefficients.l E
        (P.frobeniusSchemeMap T₀) ≅
      integralOperationsPullbackTowerFunctor P.coefficients.l E
        (P.frobeniusGaloisMap T₀),
      ∀ (Q : CochainComplex
        (integralTowerModules P.coefficients.l E (P.frobeniusFiber T₀).left) ℤ)
        (n : ℕ),
        (κ.hom.app Q).app (op n) = (P.kappaStrictLevel E T₀ n).hom.app Q := by
  sorry

/-- The strict map is fixed on every level, degree and section, including transitions.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaStrict
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :=
  (P.kappaStrict_existsUnique E T₀).exists.choose

/-- The integral comparison is uniquely determined by the whole-system Roos map.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: apply the functorial Roos construction to the strict map and its inverse.
Whisker with the good-complex inclusion and localize. Conjugate by the two
recorded representative comparisons. The good-complex localization is a
localization at quasi-isomorphisms, so the natural map descends uniquely. Its
inverse descends in the same way; the strict inverse identities prove that the
descended maps are inverse. The normalization uses a map of entire towers,
rather than inferring equality from finite-level derived evaluations. -/
theorem kappaIntegral_existsUnique
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    ∃! κ : integralDerivedPullback P.coefficients.l E
        (P.frobeniusSchemeMap T₀) ≅
      integralDerivedPullback P.coefficients.l E (P.frobeniusGaloisMap T₀),
      ∀ Q : (integralOperationsGoodComplex P.coefficients.l E
        (P.frobeniusFiber T₀).left).FullSubcategory,
        (integralDerivedPullbackComparison P.coefficients.l E
            (P.frobeniusSchemeMap T₀)).hom.app Q ≫
          DerivedCategory.Q.map
            (integralOperationsRoosFunctor.map ((P.kappaStrict E T₀).hom.app Q.obj)) =
        κ.hom.app ((integralOperationsGoodLocalization P.coefficients.l E
          (P.frobeniusFiber T₀).left).obj Q) ≫
          (integralDerivedPullbackComparison P.coefficients.l E
            (P.frobeniusGaloisMap T₀)).hom.app Q := by
  sorry

/-- The completed κ is the uniquely normalized descent of the specified strict map.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaIntegral
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :=
  (P.kappaIntegral_existsUnique E T₀).exists.choose

/-- The prime-invertibility structure inherited from the fixed geometric fibre.
Source: the purity coefficient convention
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
instance kappaPrimeInvertible
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    ∀ x : (P.frobeniusFiber T₀).left,
      Invertible (P.coefficients.l : (P.frobeniusFiber T₀).left.residueField x) :=
  sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different T₀

/-- Restriction of the actual completed comparison to constructible objects.
Source: the integral scheme-Frobenius form
(blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: constructible pullbacks are full-subcategory restrictions of the two
completed pullbacks. Full faithfulness lifts each component of the completed
isomorphism uniquely; its naturality and inverse identities lift as well. -/
theorem kappaConstructible_existsUnique
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    ∃! κ : constructibleIntegralPullback P.coefficients.l E (P.frobeniusSchemeMap T₀) ≅
      constructibleIntegralPullback P.coefficients.l E (P.frobeniusGaloisMap T₀),
      ∀ K : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left,
        (κ.hom.app K).hom = (P.kappaIntegral E T₀).hom.app K.obj := by
  sorry

/-- The full-subcategory lift of the completed comparison.
Source: the integral scheme-Frobenius form
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaConstructible (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  (P.kappaConstructible_existsUnique E T₀).exists.choose

/-- The rational comparison is the scalar localization of the integral comparison.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: localize the integral natural isomorphism. On a pure scalar tensor,
naturality is the scalar multiple of integral naturality; additivity extends it
to every arrow. The recorded rational pullbacks have exactly these object and
Hom formulas. The displayed component condition therefore specifies a unique
natural isomorphism between those actual functors. -/
theorem kappaRational_existsUnique
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    ∃! κ : rationalDerivedPullback P.coefficients.l E (P.frobeniusSchemeMap T₀) ≅
      rationalDerivedPullback P.coefficients.l E (P.frobeniusGaloisMap T₀),
      ∀ K : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left,
        HEq (κ.hom.app K)
          ((sfRationalConstructibleLocalization P.coefficients.l E
            (P.frobeniusFiber T₀).left).map ((P.kappaConstructible E T₀).hom.app K.obj)) := by
  sorry

/-- The uniquely normalized rational comparison, using the actual scalar localization.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaRational (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  (P.kappaRational_existsUnique E T₀).exists.choose

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The common-stage comparison has exactly the normalized rational representatives.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-coefficient-stage-comparisons).
Proof: represent each object and arrow over a common finite coefficient field.
Conjugate the rational κ by the two recorded common-stage pullback comparisons.
The integral scalar equation, then its scalar localization, shows invariance
under further extension. It therefore respects eventual equality of arrow
representatives. Naturality and inverse identities hold over the common finite
field. Every arrow has such a representative; its prescribed formula gives
uniqueness. This uses the existing pair category and adds no retracts. -/
theorem kappaCommon_existsUnique
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    ∃! κ : commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
        (P.frobeniusSchemeMap T₀) ≅
      commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
        (P.frobeniusGaloisMap T₀),
      ∀ (N : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
        P.coefficients.Qbar (P.frobeniusFiber T₀).left)
        (L : Index P.coefficients.l P.coefficients.Qbar) (h : N.stage ≤ L),
        HEq (κ.hom.app N)
          (ofHom
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
              (P.frobeniusSchemeMap T₀) N)
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
              (P.frobeniusGaloisMap T₀) N) L h h
            ((commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
                (P.frobeniusSchemeMap T₀) N L h).hom ≫
              (P.kappaRational (AlgebraicallyClosedCoefficients.Coefficient.{u}
                  P.coefficients.l P.coefficients.Qbar L)
                T₀).hom.app (N.toStage h) ≫
              (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
                (P.frobeniusGaloisMap T₀) N L h).inv)) := by
  sorry

/-- The actual common-stage comparison, uniquely fixed on all representatives.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaCommon (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  (P.kappaCommon_existsUnique T₀).exists.choose
/-- The finite correspondence on data and all equivariant arrows is the existing
algebra equivalence. Its forward functor sends φ to κ followed by φ; its inverse
uses κ inverse. Being functors, both directions preserve identities, composition,
and every pasted finite diagram.
Source: Returned Step 11, step 7
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaFiniteEquivariance
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :=
  Endofunctor.Algebra.equivOfNatIso (P.schemeGeometricFrobeniusComparison T₀).symm

/-- The same actual algebra equivalence at completed integral coefficients.
Source: Returned Step 11, step 7
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaIntegralEquivariance (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  Endofunctor.Algebra.equivOfNatIso (P.kappaConstructible E T₀).symm

/-- The same actual algebra equivalence at rational coefficients.
Source: Returned Step 11, step 7
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaRationalEquivariance (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  Endofunctor.Algebra.equivOfNatIso (P.kappaRational E T₀).symm

/-- The same actual algebra equivalence in the existing common-stage category.
Source: Returned Step 11, step 7
(blueprint: def-pur-kappa-coefficient-stage-comparisons). -/
def kappaCommonEquivariance (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  Endofunctor.Algebra.equivOfNatIso (P.kappaCommon T₀).symm


end WeilConjectures.PurityFiniteSetting
