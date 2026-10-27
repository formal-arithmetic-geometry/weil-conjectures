# WeilConjectures.PointRationalNormalization: canonical coefficient helpers

## Reason

The parent descent theorem uses the canonical small coefficient fields `Coefficient.{u} l Ω F = Shrink F.val`. Two stated dependencies used literal subfields instead, so the supplied family could not be passed to them. Align their indexed assertions with the prescribed small fields and conjugated inclusions. This is transport along the canonical algebra equivalences, with no new hypothesis.

The first complete assembly exceeded the 60-second compile limit. A profiler probe showed Lean unfolding duplicated integral/rational helpers through derived localizations and size transports while matching interfaces. Replace the duplicate helpers by abbreviations of their existing owners. The common-stage owner is `PointRationalFamilyCommonStageNaturality`; the integral owner is `PointTransformationRationalNormalization`. Every alias expands to the original construction. No natural transformation components, comparisons, or transport maps are chosen or replaced. This follows the one-definition-per-notion requirement.

## Old

```lean
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.CoefficientComplexRationalization
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Linear.Basic
import Sheaf.CategoryTheory.ScalarLocalization

def rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalDerivedPullback l E g

def b (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  (pointRationalFibre D l hl L).mapIso
      ((rationalAlpha D l hl g E L ι).app K).symm ≪≫
    (pointRationalFibreScalarIso D l hl E L ι).app
      ((rationalPullback D l hl g E).obj K)

def IntegralFamily :=
  ∀ F : Padic.FiniteCoefficientFields l Ω,
    sections D l F.val ⟶ pullback D l hl g F.val ⋙ sections D l F.val

def IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfIntegralConstructibleCategory l F.val (Spec (.of D.k))),
    (η G).app ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F.val G.val
        (IntermediateField.inclusion h) (Spec (.of D.k))).obj K) ≫
      (sections D l G.val).map
        (alpha D l hl g F.val G.val (IntermediateField.inclusion h) K).inv ≫
      (phi D l hl F.val G.val (IntermediateField.inclusion h)
        ((pullback D l hl g F.val).obj K)).hom =
    (phi D l hl F.val G.val (IntermediateField.inclusion h) K).hom ≫
      (pointIntegralModuleDerivedTensor l F.val G.val (IntermediateField.inclusion h)).map
        ((η F).app K)

def RationalFamily :=
  ∀ F : Padic.FiniteCoefficientFields l Ω,
    pointRationalFibre D l hl F.val ⟶
      rationalPullback D l hl g F.val ⋙ pointRationalFibre D l hl F.val

def Components (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl F.val K).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} F.val).mapDerivedCategory.map ((t F).app K).hom ≫
        (pointRationalNormalization D l hl F.val
          ((rationalPullback D l hl g F.val).obj K)).hom)
      ((pointModuleDerivedRationalization l F.val).map ((η F).app K.obj))

def TensorActions (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K M : sfIntegralConstructibleCategory l F.val (Spec (.of D.k))),
    (∀ (v : K ⟶ M) (a : F.val),
      HEq ((pointRationalFibre D l hl F.val).map (tensorArrow D l F.val K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl F.val).map v).hom) ∧
      HEq ((rationalPullback D l hl g F.val ⋙ pointRationalFibre D l hl F.val).map
        (tensorArrow D l F.val K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl F.val).map
          ((pullback D l hl g F.val).map v)).hom)) ∧
    (∀ (n : ℕ) (v : Fin n → (K ⟶ M)) (a : Fin n → F.val),
      (pointRationalFibre D l hl F.val).map
          (∑ j, tensorArrow D l F.val K M (v j) (a j)) ≫
        (t F).app ((sfRationalConstructibleLocalization l F.val (Spec (.of D.k))).obj M) =
      (t F).app ((sfRationalConstructibleLocalization l F.val (Spec (.of D.k))).obj K) ≫
        (rationalPullback D l hl g F.val ⋙ pointRationalFibre D l hl F.val).map
          (∑ j, tensorArrow D l F.val K M (v j) (a j)))

def ScalarCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (t G).app ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val (IntermediateField.inclusion h)).obj K) ≫
      (b D l hl g F.val G.val (IntermediateField.inclusion h) K).hom =
    (pointRationalFibreScalarIso D l hl F.val G.val (IntermediateField.inclusion h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map
        ((t F).app K)

def ComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    HEq ((rationalAlpha D l hl g F.val G.val (IntermediateField.inclusion h)).hom.app K)
      ((sfRationalConstructibleLocalization l G.val (Spec (.of D.k))).map
        (alpha D l hl g F.val G.val (IntermediateField.inclusion h) K.obj).hom) ∧
    HEq ((rationalAlpha D l hl g F.val G.val (IntermediateField.inclusion h)).inv.app K)
      ((sfRationalConstructibleLocalization l G.val (Spec (.of D.k))).map
        (alpha D l hl g F.val G.val (IntermediateField.inclusion h) K.obj).inv)

def SectionsComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl G.val
          ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val
            (IntermediateField.inclusion h)).obj K)).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} G.val).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl F.val G.val
            (IntermediateField.inclusion h)).hom.app K).hom) ≫
        (pointFibreTensorLiftIso l F.val G.val (IntermediateField.inclusion h)).hom.app
          ((pointRationalFibre D l hl F.val).obj K).obj ≫
        (pointCoefficientFieldDerivedTensor l F.val G.val (IntermediateField.inclusion h)).map
          (pointRationalNormalization D l hl F.val K).hom)
      (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr
          K.obj.property)).hom ∧
    HEq
      ((pointCoefficientFieldDerivedTensor l F.val G.val (IntermediateField.inclusion h)).map
          (pointRationalNormalization D l hl F.val K).inv ≫
        (pointFibreTensorLiftIso l F.val G.val (IntermediateField.inclusion h)).inv.app
          ((pointRationalFibre D l hl F.val).obj K).obj ≫
        (ModuleCat.uliftFunctor.{u + 1, u} G.val).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl F.val G.val
            (IntermediateField.inclusion h)).inv.app K).hom) ≫
        (pointRationalNormalization D l hl G.val
          ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val
            (IntermediateField.inclusion h)).obj K)).hom)
      (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr
          K.obj.property)).inv

def ComparisonCoherence : Prop :=
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (rationalAlpha D l hl g F.val F.val (AlgHom.id ℚ_[l] F.val)).hom.app K ≫
        (rationalPullback D l hl g F.val).map
          ((sfRationalScalarUnit l F.val (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) =
      (sfRationalScalarUnit l F.val (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalPullback D l hl g F.val).obj K)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (sfRationalScalarExtension l G.val (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) H.val (IntermediateField.inclusion j)).map
        ((rationalAlpha D l hl g F.val G.val (IntermediateField.inclusion h)).hom.app K) ≫
      (rationalAlpha D l hl g G.val H.val (IntermediateField.inclusion j)).hom.app
        ((sfRationalScalarExtension l F.val (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) G.val (IntermediateField.inclusion h)).obj K) ≫
      (rationalPullback D l hl g H.val).map
        ((sfRationalScalarComp l F.val G.val (IntermediateField.inclusion h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) H.val
          (IntermediateField.inclusion j)).hom.app K) =
    (sfRationalScalarComp l F.val G.val (IntermediateField.inclusion h)
        (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) H.val
        (IntermediateField.inclusion j)).hom.app ((rationalPullback D l hl g F.val).obj K) ≫
      (rationalAlpha D l hl g F.val H.val
        ((IntermediateField.inclusion j).comp (IntermediateField.inclusion h))).hom.app K) ∧
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (pointRationalSectionsScalarExtensionIso l F.val F.val (AlgHom.id ℚ_[l] F.val)
        D hl K.obj.obj ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr
          K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedUnit l F.val).hom.app
        ((pointModuleDerivedRationalization l F.val).obj
          ((sections D l F.val).obj K.obj)) =
    (pointModuleDerivedRationalization l F.val).map
      ((pointCompletedDerivedSections D.k l F.val).map
        (pointIntegralScalarUnit l F.val D hl K.obj.obj
          ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr K.obj.property)).hom)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l F.val (Spec (.of D.k))),
    (pointModuleDerivedRationalization l H.val).map
      ((pointCompletedDerivedSections D.k l H.val).map
        (pointIntegralScalarAssoc l F.val G.val (IntermediateField.inclusion h) H.val
          (IntermediateField.inclusion j) D hl K.obj.obj
          ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr K.obj.property)).hom) ≫
      (pointRationalSectionsScalarExtensionIso l F.val H.val
        ((IntermediateField.inclusion j).comp (IntermediateField.inclusion h)) D hl K.obj.obj
        ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr K.obj.property)).hom =
    (pointRationalSectionsScalarExtensionIso l G.val H.val (IntermediateField.inclusion j)
        D hl _ (integralScalarExtension_constructible D l hl F.val G.val
          (IntermediateField.inclusion h) (Spec (.of D.k))
          ⟨K.obj.obj, (pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr
            K.obj.property⟩)).hom ≫
      (pointCoefficientFieldDerivedTensor l G.val H.val (IntermediateField.inclusion j)).map
        (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion h)
          D hl K.obj.obj ((pointIntegralConstructible_iff l F.val D hl K.obj.obj).mpr
            K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedAssoc l F.val G.val (IntermediateField.inclusion h) H.val
        (IntermediateField.inclusion j)).hom.app
          ((pointModuleDerivedRationalization l F.val).obj ((sections D l F.val).obj K.obj)))
```

## New

```lean
public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.CoefficientComplexRationalization
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Linear.Basic
import Sheaf.CategoryTheory.ScalarLocalization

abbrev rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

abbrev b (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalFamily.rationalB D l hl g E L ι K

def IntegralFamily :=
  ∀ F : Padic.FiniteCoefficientFields l Ω,
    sections D l (Coefficient.{u} l Ω F) ⟶ pullback D l hl g (Coefficient.{u} l Ω F) ⋙ sections D l
      (Coefficient.{u} l Ω F)

def IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (η G).app ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h) (Spec (.of D.k))).obj K) ≫
      (sections D l (Coefficient.{u} l Ω G)).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K).inv ≫
      (phi D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F G h)
        ((pullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom =
    (phi D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F G h)
      K).hom ≫
      (pointIntegralModuleDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).map
        ((η F).app K)

abbrev RationalFamily :=
  PointRationalFamily.RationalFamily D l hl Ω g

def Components (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω F)).mapDerivedCategory.map ((t
          F).app K).hom ≫
        (pointRationalNormalization D l hl (Coefficient.{u} l Ω F)
          ((rationalPullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom)
      ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).map ((η F).app K.obj))

def TensorActions (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K M : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (∀ (v : K ⟶ M) (a : (Coefficient.{u} l Ω F)),
      HEq ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).map (tensorArrow D l (Coefficient.{u}
        l Ω F) K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl (Coefficient.{u} l Ω F)).map v).hom) ∧
      HEq ((rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙ pointRationalFibre D l hl
        (Coefficient.{u} l Ω F)).map
        (tensorArrow D l (Coefficient.{u} l Ω F) K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl (Coefficient.{u} l Ω F)).map
          ((pullback D l hl g (Coefficient.{u} l Ω F)).map v)).hom)) ∧
    (∀ (n : ℕ) (v : Fin n → (K ⟶ M)) (a : Fin n → (Coefficient.{u} l Ω F)),
      (pointRationalFibre D l hl (Coefficient.{u} l Ω F)).map
          (∑ j, tensorArrow D l (Coefficient.{u} l Ω F) K M (v j) (a j)) ≫
        (t F).app ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) (Spec (.of
          D.k))).obj M) =
      (t F).app ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) (Spec (.of
        D.k))).obj K) ≫
        (rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙ pointRationalFibre D l hl
          (Coefficient.{u} l Ω F)).map
          (∑ j, tensorArrow D l (Coefficient.{u} l Ω F) K M (v j) (a j)))

abbrev ScalarCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalFamily.RationalCompatible D l hl Ω g t

def ComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
      (coefficientInclusion l Ω F G h)).hom.app K)
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω G) (Spec (.of D.k))).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K.obj).hom) ∧
    HEq ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
      (coefficientInclusion l Ω F G h)).inv.app K)
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω G) (Spec (.of D.k))).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K.obj).inv)

def SectionsComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl (Coefficient.{u} l Ω G)
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).obj K)).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω G)).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).hom.app K).hom) ≫
        (pointFibreTensorLiftIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).hom.app
          ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).obj K).obj ≫
        (pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).map
          (pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).hom)
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).hom ∧
    HEq
      ((pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).map
          (pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).inv ≫
        (pointFibreTensorLiftIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).inv.app
          ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).obj K).obj ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω G)).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).inv.app K).hom) ≫
        (pointRationalNormalization D l hl (Coefficient.{u} l Ω G)
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).obj K)).hom)
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).inv

def ComparisonCoherence : Prop :=
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F) (AlgHom.id ℚ_[l]
      (Coefficient.{u} l Ω F))).hom.app K ≫
        (rationalPullback D l hl g (Coefficient.{u} l Ω F)).map
          ((sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) =
      (sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalPullback D l hl g (Coefficient.{u} l Ω F)).obj K)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (sfRationalScalarExtension l (Coefficient.{u} l Ω G) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H) (coefficientInclusion l Ω G
          H j)).map
        ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).hom.app K) ≫
      (rationalAlpha D l hl g (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H) (coefficientInclusion
        l Ω G H j)).hom.app
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω
            F G h)).obj K) ≫
      (rationalPullback D l hl g (Coefficient.{u} l Ω H)).map
        ((sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H j)).hom.app K) =
    (sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l
      Ω F G h)
        (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).hom.app ((rationalPullback D l hl g (Coefficient.{u} l Ω
          F)).obj K) ≫
      (rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H j).comp (coefficientInclusion l Ω F G h))).hom.app K) ∧
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F)
      (AlgHom.id ℚ_[l] (Coefficient.{u} l Ω F))
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedUnit l (Coefficient.{u} l Ω F)).hom.app
        ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).obj
          ((sections D l (Coefficient.{u} l Ω F)).obj K.obj)) =
    (pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).map
      ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω F)).map
        (pointIntegralScalarUnit l (Coefficient.{u} l Ω F) D hl K.obj.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property)).hom)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (pointModuleDerivedRationalization l (Coefficient.{u} l Ω H)).map
      ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω H)).map
        (pointIntegralScalarAssoc l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H j) D hl K.obj.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property)).hom) ≫
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H j).comp (coefficientInclusion l Ω F G h)) D hl K.obj.obj
        ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
          K.obj.property)).hom =
    (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H)
      (coefficientInclusion l Ω G H j)
        D hl _ (integralScalarExtension_constructible D l hl (Coefficient.{u} l Ω F)
          (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h) (Spec (.of D.k))
          ⟨K.obj.obj, (pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property⟩)).hom ≫
      (pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).map
        (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
            K.obj.obj).mpr
            K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedAssoc l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).hom.app
          ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).obj ((sections D l
            (Coefficient.{u} l Ω F)).obj K.obj)))
```

The imported common-stage module supplies definitions only to the repaired
dependencies; its theorem is not used to assume comparison coherence or normalization.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointTransformationRationalNormalization | unclaimed | rationalPullback, b, IntegralFamily, IntegralCompatible, RationalFamily, Components, TensorActions, ScalarCompatible, ComparisonNormalization, SectionsComparisonNormalization, ComparisonCoherence use canonical owners/models. |
| Sheaf.Paper.PointTransformationCoefficientDescent | R4 | Uses the corrected interface in the proof and aliases. |

The downstream script reports zero existing downstream modules for each of the three edited modules. Repository-wide namespace searches find no external uses of either repaired dependency. Existing unfinished DAG parents of the item stay valid: the aliases preserve their definitions exactly, and the theorem statement is unchanged. The two dependency nodes have only the parent descent node as a citer, audited in their statement_change records. No module held by another group is adapted. No target statement mentions a changed alias, and no target signature or mathematical meaning changes.

Identity inclusions, equal stages, zero transformations, empty sums and torsion objects retain the same formulas. No transition injectivity or component invertibility is assumed. No new theorem hole, arbitrary witness, or axiom is added.

## Status

landed 20261025T043315-L-1694914 2026-10-25 (merge of deliver/R4/Sheaf.Paper.PointTransformationCoefficientDescent)
