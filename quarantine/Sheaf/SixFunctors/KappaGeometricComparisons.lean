module

public import Sheaf.Paper.PurityKappaStages
public import Sheaf.Paper.RealizedPullbackComparisons
public import Sheaf.Paper.SimultaneousIntegralPullbackComparisons
public import Sheaf.Paper.OrdinaryPullbackCompositionEvaluation
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
public import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
public import Sheaf.Paper.NormalizedPullbackCompositionTransport
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Canonical geometric square comparisons for κ

Source: Returned Step 11, steps 2--6
(blueprint: def-pur-kappa-geometric-compositors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.PurityFiniteSetting

/-- Both Frobenius endomorphisms commute with an arbitrary base-changed arrow.
Source: Returned Step 11, step 2
(blueprint: def-pur-kappa-geometric-compositors).
Proof: naturality of absolute Frobenius gives the scheme-Frobenius equation on
both projections of the base-change fibre. The geometric-Galois equation holds
on those projections because the original arrow is defined over k₀. Pullback
extensionality gives both equalities. No Cartesianity or smoothness is used. -/
theorem kappaGeometricSquares (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))} (u₀ : T'₀ ⟶ T₀) :
    P.frobeniusMap u₀ ≫ P.frobeniusGaloisMap T₀ =
        P.frobeniusGaloisMap T'₀ ≫ P.frobeniusMap u₀ ∧
      P.frobeniusMap u₀ ≫ P.frobeniusSchemeMap T₀ =
        P.frobeniusSchemeMap T'₀ ≫ P.frobeniusMap u₀ := by
  sorry

/-- The actual geometric-Galois square compositor, with its equality transport.
Source: Returned Step 11, step 2
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaGeometricG (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))} (u₀ : T'₀ ⟶ T₀) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T'₀) :=
  (P.frobeniusDerivedComposition (P.frobeniusMap u₀)
      (P.frobeniusGaloisMap T₀)).symm ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
      (P.kappaGeometricSquares u₀).1) ≪≫
    P.frobeniusDerivedComposition (P.frobeniusGaloisMap T'₀) (P.frobeniusMap u₀)

/-- The actual scheme-Frobenius square compositor, without a Cartesian hypothesis.
Source: Returned Step 11, step 2
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaGeometricH (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))} (u₀ : T'₀ ⟶ T₀) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T'₀) :=
  (P.frobeniusDerivedComposition (P.frobeniusMap u₀)
      (P.frobeniusSchemeMap T₀)).symm ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
      (P.kappaGeometricSquares u₀).2) ≪≫
    P.frobeniusDerivedComposition (P.frobeniusSchemeMap T'₀) (P.frobeniusMap u₀)

/-- The recorded simultaneous system, with all representative and whole-counit
normalizations retained. This is fixed outside the coefficient and scheme quantifiers.
Its realization maps are the normalized models of the published pullback, not
freely chosen isomorphisms.
Source: `lem-trf-integral-pullback-comparison-realization`
(blueprint: def-pur-kappa-geometric-compositors). -/
@[irreducible] def kappaRealizationSystem (P : PurityFiniteSetting.{u}) :
    IntegralComparisonSystem.{u} P.coefficients.l :=
  (integralPullbackComparisonRealization_simultaneous P.coefficients.l).choose

/-- The integral square uses the recorded strict-system-normalized compositors.
Source: Returned Step 11, steps 2 and 4
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaIntegralSquare (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (geometric : Bool)
    (K : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left) :
    (constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).obj
        ((constructibleIntegralPullback P.coefficients.l E
          (if geometric then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj K) ≅
      (constructibleIntegralPullback P.coefficients.l E
        (if geometric then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀)).obj
          ((constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).obj K) :=
  (integralComparisonConstructibleComposition P.coefficients.l E
    P.kappaRealizationSystem (P.frobeniusMap u₀)
      (if geometric then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) K).symm ≪≫
    eqToIso (congrArg
      (fun f ↦ (constructibleIntegralPullback P.coefficients.l E f).obj K)
      (Bool.rec (motive := fun b ↦
        P.frobeniusMap u₀ ≫
            (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) =
          (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀) ≫
            P.frobeniusMap u₀)
        (P.kappaGeometricSquares u₀).2 (P.kappaGeometricSquares u₀).1 geometric)) ≪≫
    integralComparisonConstructibleComposition P.coefficients.l E P.kappaRealizationSystem
      (if geometric then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀)
      (P.frobeniusMap u₀) K

/-- The actual relative-Frobenius isomorphism of the small site.
Source: relative-Frobenius projection formula
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaRelativeFrobenius (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :=
  (absoluteFrobenius_proEtale_trivialization_pullback
    P.field.p P.field.prime P.Ring).choose (P.frobeniusFiber T₀).left
      ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
        (P.field.model_characteristic
          (pullback.fst T₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom))⟩
      P.field.a

/-- Raw-coordinate quotient functor, with the actual positive quotient ring map.
Source: `lem-fix-operation-reduction`
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaRawReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :=
  ProEtale.directImageScalarExtension (P.finiteReductionRingHom m hm hmn) T

/-- Its normalized scalar/pullback comparison, oriented from scalar after pullback.
Source: `lem-fix-operation-reduction`
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaRawReductionPullback (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.directImageScalarPullbackIso (P.finiteReductionRingHom m hm hmn) f).symm

/-- The rational square compositor is the localization of the specified integral one.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-geometric-compositors).
Proof: localize the integral square compositor. The rational pullback object
and pure-tensor Hom formulas identify its endpoints with the recorded rational
composites. Naturality follows by scalar linearity, and the integral inverse
localizes to its inverse. The component formula determines it uniquely. -/
theorem kappaRationalSquare_existsUnique (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (geometric : Bool) :
    ∃! c : rationalDerivedPullback P.coefficients.l E
        (if geometric then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
          rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀) ≅
      rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀) ⋙
        rationalDerivedPullback P.coefficients.l E
          (if geometric then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀),
      ∀ N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left,
        HEq (c.hom.app N)
          ((sfRationalConstructibleLocalization P.coefficients.l E
            (P.frobeniusFiber T'₀).left).map
              (P.kappaIntegralSquare E u₀ geometric N.obj).hom) := by
  sorry

/-- The canonical rational compositor, with its integral normalization retained.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaRationalSquare (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (geometric : Bool) :=
  (P.kappaRationalSquare_existsUnique E u₀ geometric).exists.choose

/-- Base change preserves identities, in the actual scheme-map presentation.
Source: canonical pullback functor (blueprint: def-pur-kappa-geometric-compositors).
Proof: apply the identity law of the base-change functor and then the forgetful
functor from the slice category to schemes. -/
theorem kappaMapId (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    P.frobeniusMap (𝟙 T₀) = 𝟙 (P.frobeniusFiber T₀).left := by
  sorry

/-- Base change preserves successive arrows, in their given order.
Source: canonical pullback functor (blueprint: def-pur-kappa-geometric-compositors).
Proof: apply the composition law of the base-change functor and the slice
forgetful functor. -/
theorem kappaMapComp (P : PurityFiniteSetting.{u})
    {T''₀ T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    (v₀ : T''₀ ⟶ T'₀) (u₀ : T'₀ ⟶ T₀) :
    P.frobeniusMap (v₀ ≫ u₀) = P.frobeniusMap v₀ ≫ P.frobeniusMap u₀ := by
  sorry

/-- The identity pullback identification with its recorded termwise unit normalization.
Source: `lem-pur-proetale-derived-pullback-identity`
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaIdentity (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap (𝟙 T₀)) ≅ 𝟭 _ :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring) (P.kappaMapId T₀)) ≪≫
    proEtaleFrobeniusDerivedIso P.Ring
      ((proEtaleDerivedPullback_identity
        (P.frobeniusFiber T₀).left P.Ring).choose_spec.2.2.choose_spec.2.choose)

/-- Ordinary evaluation normalization, including every object and positive quotient.
This named predicate keeps the construction's uniqueness statement small; its data
are exactly the two normalized finite presentation maps and relative Frobenius.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-geometric-compositors). -/
@[irreducible] def KappaSequenceNormalization (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    (κ : integralComparisonSequencePullback P.coefficients.l E
        (P.frobeniusSchemeMap T₀) ≅
      integralComparisonSequencePullback P.coefficients.l E (P.frobeniusGaloisMap T₀)) : Prop :=
      ∀ (N : coefficientSequenceModules P.coefficients.l E (P.frobeniusFiber T₀).left)
        (n : ℕ),
        (coefficientSequenceEvaluation P.coefficients.l E (P.frobeniusFiber T₀).left n).map
            (κ.hom.app N) ≫
          (PullbackCompositionTransport.ordinaryEvaluation P.coefficients.l E
            (P.frobeniusGaloisMap T₀) n).hom.app N =
        (PullbackCompositionTransport.ordinaryEvaluation P.coefficients.l E
            (P.frobeniusSchemeMap T₀) n).hom.app N ≫
          (integralFinitePullbackModel P.coefficients.l E (P.frobeniusSchemeMap T₀) n ≪≫
            P.kappaOrdinaryFor (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)) T₀ ≪≫
            (integralFinitePullbackModel P.coefficients.l E
              (P.frobeniusGaloisMap T₀) n).symm).hom.app
                ((coefficientSequenceEvaluation P.coefficients.l E
                  (P.frobeniusFiber T₀).left n).obj N)

/-- The ordinary comparison on the site of entire coefficient sequences.
Its evaluation is fixed by the same relative-Frobenius maps at every quotient.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-geometric-compositors).
Proof: use relative Frobenius on each weakly etale object and the identity on
its quotient index. These maps respect every quotient transition. Conjugate their
adjunction mates by the unit-normalized finite pullback models. Evaluation gives
the stated formula. Inverses have the same transition compatibility. Joint
faithfulness of ordinary sequence evaluation proves uniqueness before localization. -/
theorem kappaSequence_existsUnique (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    ∃! κ : integralComparisonSequencePullback P.coefficients.l E
        (P.frobeniusSchemeMap T₀) ≅
      integralComparisonSequencePullback P.coefficients.l E (P.frobeniusGaloisMap T₀),
        P.KappaSequenceNormalization E T₀ κ := by
  sorry

/-- The unique actual strict-system map with the specified finite restrictions.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-geometric-compositors). -/
@[irreducible] def kappaSequence (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    integralComparisonSequencePullback P.coefficients.l E (P.frobeniusSchemeMap T₀) ≅
      integralComparisonSequencePullback P.coefficients.l E (P.frobeniusGaloisMap T₀) :=
  (P.kappaSequence_existsUnique E T₀).exists.choose

/-- The actual completed κ is also the realization of the specified sequence-site
κ under the same whole-system models that define the integral compositors.
Source: Returned Step 11, step 4
(blueprint: def-pur-kappa-geometric-compositors). -/
@[irreducible] def KappaSequenceRealization (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) : Prop :=
  ∀ K : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left,
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left K.obj →
    (P.kappaIntegral E T₀).hom.app K.obj ≫
      ((P.kappaRealizationSystem.coefficient E).pullback
        (P.frobeniusGaloisMap T₀)).realization.hom.app K.obj =
    ((P.kappaRealizationSystem.coefficient E).pullback
        (P.frobeniusSchemeMap T₀)).realization.hom.app K.obj ≫
      (coefficientSequenceLimit P.coefficients.l E (P.frobeniusFiber T₀).left).map
        ((Functor.mapDerivedCategoryNatIso (P.kappaSequence E T₀)).hom.app
          (((P.kappaRealizationSystem.coefficient E).system
            (P.frobeniusFiber T₀).left).reduction.obj K.obj))

/-- The commuting geometric square on the entire ordinary sequence site.
Both compositors are the recorded adjunction-normalized strict maps; the middle
map transports the actual equality of scheme maps for the base change of `u₀`.
Source: Returned Step 11, steps 2--4
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaSequenceSquare (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))} (u₀ : T'₀ ⟶ T₀) (b : Bool) :
    integralComparisonSequencePullback P.coefficients.l E
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
      integralComparisonSequencePullback P.coefficients.l E (P.frobeniusMap u₀) ≅
    integralComparisonSequencePullback P.coefficients.l E (P.frobeniusMap u₀) ⋙
      integralComparisonSequencePullback P.coefficients.l E
        (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀) :=
  (integralComparisonSequenceComposition P.coefficients.l E (P.frobeniusMap u₀)
    (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).symm ≪≫
    eqToIso (congrArg (integralComparisonSequencePullback P.coefficients.l E)
      (Bool.rec (motive := fun c ↦ P.frobeniusMap u₀ ≫
          (if c then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) =
        (if c then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀) ≫
          P.frobeniusMap u₀)
        (P.kappaGeometricSquares u₀).2 (P.kappaGeometricSquares u₀).1 b)) ≪≫
    integralComparisonSequenceComposition P.coefficients.l E
      (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀) (P.frobeniusMap u₀)

/-- The canonical compositor for two actual base-changed arrows.
Source: `lem-trf-derived-pullback-coherence`
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaPullbackComposition (P : PurityFiniteSetting.{u})
    {T''₀ T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    (v₀ : T''₀ ⟶ T'₀) (u₀ : T'₀ ⟶ T₀) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap (v₀ ≫ u₀)) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap v₀) :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
    (P.kappaMapComp v₀ u₀)) ≪≫
      P.frobeniusDerivedComposition (P.frobeniusMap v₀) (P.frobeniusMap u₀)

/-- The two specified square compositors as one dependent family.
Source: Returned Step 11, step 2
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaFiniteSquare (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))} (u₀ : T'₀ ⟶ T₀) (b : Bool) :
    proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
          proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring
          (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀) :=
  Bool.rec (motive := fun c ↦
    proEtaleConstantRingDerivedPullback P.Ring
        (if c then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
          proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring
          (if c then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀))
    (P.kappaGeometricH u₀) (P.kappaGeometricG u₀) b

/-- The prescribed common-stage comparison for an iterated pullback.
Source: common-stage representative formulas
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaCommonCompositeModel (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
    (N : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Z)
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (h : N.stage ≤ L) :=
  commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar f
      (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar g N) L h ≪≫
    (rationalDerivedPullback P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u}
        P.coefficients.l P.coefficients.Qbar L) f).mapIso
      (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar g N L h)

/-- Common-stage geometric compositors are determined by their actual representatives.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-geometric-compositors).
Proof: at every common field, use the normalized rational square compositor and
conjugate by the two common-stage composite models. Scalar compatibility of
the integral compositor, then scalar localization, shows that this formula is
preserved by enlargement. Thus it defines a map of the actual pair category.
The inverse formula descends as well. Naturality and inverse identities can be
tested at one common finite stage. Every representative is covered by the
displayed formula, which proves uniqueness without any choice of comparison data. -/
theorem kappaCommonSquare_existsUnique (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (b : Bool) :
    ∃! c : commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
          commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
            (P.frobeniusMap u₀) ≅
      commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar (P.frobeniusMap u₀) ⋙
        commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
          (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀),
      ∀ (N : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
        P.coefficients.Qbar (P.frobeniusFiber T₀).left)
        (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
        (h : N.stage ≤ L),
        HEq (c.hom.app N)
          (GeneralAlgebraicallyClosedCoefficients.ofHom
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (P.frobeniusMap u₀)
              (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
                (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) N))
            (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
              (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀)
              (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
                (P.frobeniusMap u₀) N)) L h h
            ((P.kappaCommonCompositeModel (P.frobeniusMap u₀)
                (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) N L h).hom ≫
              (P.kappaRationalSquare (AlgebraicallyClosedCoefficients.Coefficient.{u}
                P.coefficients.l P.coefficients.Qbar L) u₀ b).hom.app (N.toStage h) ≫
              (P.kappaCommonCompositeModel
                (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀)
                (P.frobeniusMap u₀) N L h).inv)) := by
  sorry

/-- The specified common-stage square compositor.
Source: Returned Step 11, step 6
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaCommonSquare (P : PurityFiniteSetting.{u})
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (b : Bool) :=
  (P.kappaCommonSquare_existsUnique u₀ b).exists.choose

/-- The integral scalar/pullback comparison as a natural isomorphism, retaining
the recorded component maps rather than selecting new comparisons.
Source: `lem-fix-operation-reduction`
(blueprint: def-pur-kappa-geometric-compositors).
Proof: the components are the completed scalar comparison, conjugated by the
natural completion isomorphisms. Thus they are natural. Each is invertible;
their inverses are natural as well. Components determine a natural isomorphism. -/
theorem kappaIntegralScalarComparison_existsUnique (P : PurityFiniteSetting.{u})
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)] :
    ∃! j : constructibleIntegralPullback P.coefficients.l E f ⋙
        sfConstructibleIntegralScalarExtension 0 P.coefficients.l
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι X ≅
      sfConstructibleIntegralScalarExtension 0 P.coefficients.l
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι Y ⋙
        constructibleIntegralPullback P.coefficients.l L f,
      ∀ N, j.hom.app N = (integralPullbackScalarComparison P.coefficients.l E L ι f N).hom := by
  sorry

/-- The recorded integral scalar/pullback components, bundled naturally.
Source: `lem-fix-operation-reduction`
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaIntegralScalarComparison (P : PurityFiniteSetting.{u})
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)] :=
  (P.kappaIntegralScalarComparison_existsUnique E L ι f).exists.choose

/-- The completed square compositors as one normalized natural isomorphism.
Source: Returned Step 11, steps 2 and 4
(blueprint: def-pur-kappa-geometric-compositors).
Proof: the canonical integral compositors are natural. Equality transport along
the commuting square is natural, so their displayed composite is natural. The
componentwise inverse gives its inverse, and components give uniqueness. -/
theorem kappaIntegralSquareNat_existsUnique (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (b : Bool) :
    ∃! c : constructibleIntegralPullback P.coefficients.l E
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀) ⋙
          constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀) ≅
      constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀) ⋙
        constructibleIntegralPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T'₀ else P.frobeniusSchemeMap T'₀),
      ∀ N, c.hom.app N = (P.kappaIntegralSquare E u₀ b N).hom := by
  sorry

/-- The normalized integral square family as a natural isomorphism.
Source: Returned Step 11, steps 2 and 4
(blueprint: def-pur-kappa-geometric-compositors). -/
def kappaIntegralSquareNat (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (b : Bool) :=
  (P.kappaIntegralSquareNat_existsUnique E u₀ b).exists.choose

end WeilConjectures.PurityFiniteSetting
