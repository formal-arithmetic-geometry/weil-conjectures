/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.SignedTwistReductionComparison
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Section coordinates and fixed comparisons on signed point Tate lines

Source: main-20261015, def-weil-frobenius-coefficient-twists, finite-reduction
and scalar-extension sentence; Deligne, Weil II (1.1.3), p. 150.
(blueprint: def-pur-point-tate-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Retain the point target's published small derived Hom universe. The residue-lisse
-- API's standard-size instance otherwise captures module categories at a larger size.
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The final pro-etale object, with the variance of sections.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev finalObject := op (ProEt.mk (𝟙 (Spec (CommRingCat.of D.k))))

/-- Integral sections with the published constant-to-completion scalar action.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev integral (m : ℤ) :=
  (pointCompletedSections D.k l E).obj (integralTwistLine l E (Spec (.of D.k)) m)

/-- Finite sections, with their coefficient size lift removed by restriction.
The natural index n denotes the positive quotient exponent n+1.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev finite (n : ℕ) (m : ℤ) :=
  (ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom).obj
    ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
      (finiteCoefficientTwist l E (Spec (.of D.k)) n m))

/-- Rational sections are exactly ordinary fraction-field tensor of integral sections.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev rational (m : ℤ) := (pointModuleRationalization l E).obj (integral D l E m)

/-- The prescribed positive root tensor, including the coefficient unit at zero.
Source: signed generators (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev positiveGenerator
    (e : (purTwistZlOne (Spec (.of D.k)) l).obj.obj (finalObject D)) (r : ℕ) :=
  FrobeniusCoefficientTwists.generator l E (Spec (.of D.k)) (finalObject D) 1 r (fun _ ↦ e)

/-- The unique normalized quotient family supplied by signed sheaf reduction.
Source: finite reduction (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def reduction (hl : l ≠ D.p) (n : ℕ) :=
  letI := frobeniusPointPrimeInvertible D l hl
  ((signedTwistReduction_comparison l E (Spec (.of D.k))).1 n).exists.choose

/-- The root section read in the fixed algebraic closure through the Spec identification.
Source: compatible roots (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev rootValue (N : ℕ)
    (x : (proEtaleRootsOfUnitySheaf (Spec (.of D.k)) N).obj.obj (finalObject D)) : D.k :=
  (ΓSpecIso (CommRingCat.of D.k)).hom.hom
    (proEtaleRootsOfUnitySections (Spec (.of D.k)) N (finalObject D) x).toMul.val.val


/-- Finite comparison maps, with positive levels encoded by their predecessor.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev FiniteComparisons := ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ) (m : ℤ),
  (ModuleCat.extendScalars (Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l E (n + 1)))).obj (integral D l E m) ≅ finite D l E n m

/-- Integral comparison maps on actual point section modules.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev IntegralComparisons := ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (m : ℤ),
  (pointIntegralModuleTensor l E L ι).obj (integral D l E m) ≅ integral D l L m

/-- The ordinary sheaf comparisons underlying the completed comparison.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev SheafComparisons := ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (m : ℤ),
  (completedOrdinaryScalarExtension l E L ι (Spec (.of D.k))).obj
    (integralTwistLine l E (Spec (.of D.k)) m) ≅ integralTwistLine l L (Spec (.of D.k)) m

/-- Rational comparison maps on the specified localizations of integral sections.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
abbrev RationalComparisons := ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (m : ℤ),
  (ModuleCat.extendScalars ι.toRingHom).obj (rational D l E m) ≅ rational D l L m

/-- The completion comparison followed by ordinary tensor and the signed line map.
This supplies the precise meaning of the completed identification of the Tate line.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def completedLineComparison (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) (β : SheafComparisons D l) :=
  letI := frobeniusPointPrimeInvertible D l hl
  (pointConstructibleCompletionIso l E L ι D hl (sfIntegralTwistingObject l E (Spec (.of D.k)) m)
    ((pointIntegralConstructible_iff l E D hl _).mpr
      (sfIntegralTwistingObject_mem l E (Spec (.of D.k)) m))).symm ≪≫
  (pointOrdinaryDerivedComparison D.k l E L ι).app
    (sfIntegralTwistingObject l E (Spec (.of D.k)) m) ≪≫
  ((completedOrdinaryScalarExtension l E L ι (Spec (.of D.k))).mapDerivedCategorySingleFunctor
    0).app (integralTwistLine l E (Spec (.of D.k)) m) ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso (β E L ι m)

/-- The canonical derived comparison in the section-module coordinates of a single line.
Source: point comparisons (blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def completedSectionsComparison (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) (β : SheafComparisons D l) :=
  letI := frobeniusPointPrimeInvertible D l hl
  ((pointIntegralModuleTensor l E L ι).mapDerivedCategorySingleFunctor 0).inv.app
      (integral D l E m) ≫
  (pointIntegralModuleDerivedTensor l E L ι).map
    (((pointCompletedSections D.k l E).mapDerivedCategorySingleFunctor 0).inv.app
      (integralTwistLine l E (Spec (.of D.k)) m)) ≫
  (pointSectionsScalarExtensionIso l E L ι D hl
    (sfIntegralTwistingObject l E (Spec (.of D.k)) m)
    ((pointIntegralConstructible_iff l E D hl _).mpr
      (sfIntegralTwistingObject_mem l E (Spec (.of D.k)) m))).inv ≫
  (pointCompletedDerivedSections D.k l L).map
    (completedLineComparison D l E hl L ι m β).hom ≫
  ((pointCompletedSections D.k l L).mapDerivedCategorySingleFunctor 0).hom.app
    (integralTwistLine l L (Spec (.of D.k)) m)


/-- Evaluate the actual internal dual at the final slice identity.
Source: negative generators
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def integralEvaluate (r : ℕ) (f : integral D l E (Int.negSucc r))
    (x : integral D l E ((r + 1 : ℕ) : ℤ)) :
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))).obj.obj
      (finalObject D) :=
  f.app (op (Over.mk (𝟙 (finalObject D).unop))) x

/-- Evaluate the normalized residue dual, with its coefficient ring explicit.
Source: negative generators
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def finiteEvaluate (n r : ℕ) (f : finite D l E n (Int.negSucc r))
    (x : finite D l E n ((r + 1 : ℕ) : ℤ)) :
    (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj (finalObject D) :=
  f.app (op (Over.mk (𝟙 (finalObject D).unop))) x

/-- The published normalized signed scalar map at the geometric point.
Source: signed scalar comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def scalarMap (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :=
  letI := frobeniusPointPrimeInvertible D l hl
  twistScalarMaps l E (Spec (.of D.k)) L ι

/-- A signed Tate object in the actual common-stage category, with the coefficient
field transported by the recorded Shrink algebra equivalence.
Source: common-stage clause
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def twistPair (hl : l ≠ D.p) (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  ⟨F, sfRationalTwistingCoefficient l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)) m⟩

/-- The recorded point normalization on the signed twist, in ordinary degree-zero
section coordinates. Source: point localization and scalar comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def rationalLineNormalization (hl : l ≠ D.p) (m : ℤ) :=
  letI := frobeniusPointPrimeInvertible D l hl
  pointRationalNormalization D l hl E
      (sfRationalTwistingCoefficient l E (Spec (.of D.k)) m) ≪≫
    (pointModuleDerivedRationalization l E).mapIso
      (((pointCompletedSections D.k l E).mapDerivedCategorySingleFunctor 0).app
        (integralTwistLine l E (Spec (.of D.k)) m)) ≪≫
    ((pointModuleRationalization l E).mapDerivedCategorySingleFunctor 0).app
      (integral D l E m)

/-- The size-descent part of the actual point normalization, prior to coefficient
localization coordinates. Source: point localization
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def rationalSizeNormalization (hl : l ≠ D.p) (m : ℤ) :
    letI := frobeniusPointPrimeInvertible D l hl
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}.obj
        ((pointRationalFibre D l hl E).obj
          (sfRationalTwistingCoefficient l E (Spec (.of D.k)) m)).obj ≅
      (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
        (pointFibreCoefficientDown E)).obj
        ((pointFibreRationalAmbient D l E).obj
          (sfIntegralTwistingObject l E (Spec (.of D.k)) m)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := pointFibreSizeLift_equivalence E
  (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}.mapIso
      ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
        (pointRationalFibreObjIso D l hl E
          (sfRationalTwistingCoefficient l E (Spec (.of D.k)) m))) ≪≫
    (pointFibreLiftDownIso E).symm.app
      ((pointIntegralRationalFibre D l hl E).obj
        (sfIntegralTwistingCoefficient l E (Spec (.of D.k)) m)).obj ≪≫
    (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
      (pointFibreCoefficientDown E)).mapIso
      ((DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι.mapIso
        ((pointFibreSizeLift E).asEquivalence.counitIso.app
          (pointFibreRationalLarge D l hl E
            (sfIntegralTwistingCoefficient l E (Spec (.of D.k)) m))))

/-- The degree-zero comparison for the actual lifted, rational section functor,
followed by coefficient descent. Source: point localization
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def rawRationalSingle (m : ℤ) :
    (pointFibreRationalAmbient D l E).obj
        (sfIntegralTwistingObject l E (Spec (.of D.k)) m) ≅
      (DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} E)) 0).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).obj
            ((pointIntegralSections l E D.k).obj
              (integralTwistLine l E (Spec (.of D.k)) m))) :=
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).mapDerivedCategory.mapIso
    (((pointIntegralSections l E D.k).mapDerivedCategorySingleFunctor 0).app
      (integralTwistLine l E (Spec (.of D.k)) m)) ≪≫
  ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).mapDerivedCategorySingleFunctor 0).app
    ((pointIntegralSections l E D.k).obj (integralTwistLine l E (Spec (.of D.k)) m))

/-- The canonical integral line comparison, restricted to the intrinsic category.
Source: completed signed line comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def integralLineComparison (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) (β : SheafComparisons D l) :=
  letI := frobeniusPointPrimeInvertible D l hl
  ObjectProperty.isoMk (P := sfIntegralConstructible l L (Spec (.of D.k)))
    (X := (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj
        (sfIntegralTwistingCoefficient l E (Spec (.of D.k)) m))
    (Y := sfIntegralTwistingCoefficient l L (Spec (.of D.k)) m)
    (completedLineComparison D l E hl L ι m β)

/-- Rationalize the canonical completed line comparison, inserting the recorded
object equality of the raw rational transition. Source: finite-stage comparisons
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def rationalLineComparison (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) (β : SheafComparisons D l) :=
  letI := frobeniusPointPrimeInvertible D l hl
  eqToIso ((sfRationalScalarExtension_existsUnique l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
      (sfRationalTwistingCoefficient l E (Spec (.of D.k)) m)) ≪≫
    (sfRationalConstructibleLocalization l L (Spec (.of D.k))).mapIso
      (integralLineComparison D l E hl L ι m β)

/-- The actual point scalar comparison followed by the canonical twist identification.
Source: finite-stage point comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def rationalPointComparison (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) (β : SheafComparisons D l) :=
  letI := frobeniusPointPrimeInvertible D l hl
  (pointRationalFibreScalarIso D l hl E L ι).symm.app
      (sfRationalTwistingCoefficient l E (Spec (.of D.k)) m) ≪≫
    (pointRationalFibre D l hl L).mapIso (rationalLineComparison D l E hl L ι m β)

/-- The signed twist identification at a common coefficient stage, with the recorded
stage-system object equality inserted. Source: common-stage coefficient comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def stageLineComparison (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (F L : Padic.FiniteCoefficientFields l Ω) (h : F ≤ L) (m : ℤ)
    (β : SheafComparisons D l) :
    (twistPair D l hl Ω F m).toStage h ≅ (twistPair D l hl Ω L m).obj :=
  letI := frobeniusPointPrimeInvertible D l hl
  (eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω (Spec (.of D.k))).exists.choose_spec.1 F L h)).app
      (twistPair D l hl Ω F m).obj ≪≫
    rationalLineComparison D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F L h) m β

/-- The canonical comparison between finite-stage presentations of the same signed
Tate object. Source: common-stage coefficient comparison
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons). -/
def twistPairComparison (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (F L : Padic.FiniteCoefficientFields l Ω) (h : F ≤ L) (m : ℤ)
    (β : SheafComparisons D l) :
    twistPair D l hl Ω F m ⟶ twistPair D l hl Ω L m :=
  StageSystem.PairCategory.mkHom L h le_rfl
    ((stageLineComparison D l hl Ω F L h m β).hom ≫
      (stageLineComparison D l hl Ω L L le_rfl m β).inv)

end WeilConjectures.PointTateFiber
