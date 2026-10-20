/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange

import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfRationalizationKaroubi
/-! # The specified Hom comparison and scalar-extended evaluation

Source: current Weil blueprint, sec-proetale-coefficients/sk-def-sf-operations,
`def-weil-derived-pullback-tensor-hom`, final common-stage paragraph;
Stacks Tags 08J9, 03EO (blueprint: lem-zl-specified-hom-scalar-evaluation).

The comparisons are the recorded normalized maps, rather than arbitrary isomorphisms.
The chain formula below also identifies their actual representative construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The completed comparison after the three canonical completion identifications.
This is the existing specified comparison, transported to ordinary scalar objects.
Source: blueprint common-stage paragraph
(blueprint: lem-zl-specified-hom-scalar-evaluation). -/
def specifiedHomIdentified (X : Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E X))
    (hM : IsSfDerivedComplete l E X M) (hN : IsSfDerivedComplete l E X N) :=
  (scalarCompletion l E L ι X).app ((integralDerivedInternalHom l E X).obj (op M, N)) ≫
    (scalarHomCompleteInputs l E L ι X M N hM hN).hom ≫
    (integralDerivedInternalHom l L X).map (Prod.mkHom
      ((scalarCompletionIso l E L ι X M hM).hom.op)
      ((scalarCompletionIso l E L ι X N hN).inv))

/-- Completeness and the equality with extended evaluation for the specified maps.
Source: blueprint common-stage paragraph; Stacks 08J9, 03EO
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: (1) completeness of N implies completeness of its ambient internal Hom with M,
by lem-pur-integral-operations-scalar-extension. (2) Finite free completion gives the
three invertible quotient-map units of lem-weil-finite-free-completed-scalar-comparison.
(3) The representative calculation in specifiedHomScalarChain below identifies the
ordinary chain-Hom comparison with the transpose of extended evaluation, hence with
lem-sf-ringed-finite-free-hom-base-change. (4) Insert the inverse Hom-output unit and
the inverse first-input/direct second-input units used by scalarHomCompleted. Cancel
the output unit to obtain the displayed equality. (5) Apply the inverse closed Hom
equivalence to obtain the evaluation composite. The API orders Hom before its input;
exchanging them gives the Koszul sign (-1)^(degree(input)*degree(Hom)) in the node. -/
theorem specifiedHomScalarEvaluation
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (M N : DerivedCategory (integralTowerModules l E X))
    (hM : sfIntegralConstructible l E X M) (hN : sfIntegralConstructible l E X N) :
    IsSfDerivedComplete l E X ((integralDerivedInternalHom l E X).obj (op M, N)) ∧
    IsIso ((scalarCompletion l E L ι X).app M) ∧
    IsIso ((scalarCompletion l E L ι X).app N) ∧
    IsIso ((scalarCompletion l E L ι X).app
      ((integralDerivedInternalHom l E X).obj (op M, N))) ∧
    ((scalarCompletion l E L ι X).app
        ((integralDerivedInternalHom l E X).obj (op M, N)) ≫
      (scalarHomCompleteInputs l E L ι X M N hM.1 hN.1).hom =
      scalarHomOrdinary l E L ι X M N ≫
        (integralDerivedInternalHom l L X).map (Prod.mkHom
          ((scalarCompletionIso l E L ι X M hM.1).inv.op)
          ((scalarCompletionIso l E L ι X N hN.1).hom))) ∧
    ((scalarIntegralClosed l L X).transpose _
        ((integralOrdinaryDerivedScalar l E L ι X).obj M)
        ((integralOrdinaryDerivedScalar l E L ι X).obj N)).symm
      (specifiedHomIdentified l E L ι X M N hM.1 hN.1) =
        (scalarClosedTensor l E L ι X).inv.app
          ((integralDerivedInternalHom l E X).obj (op M, N), M) ≫
        (integralOrdinaryDerivedScalar l E L ι X).map
          ((scalarIntegralClosed l E X).evaluation M N) := by
  sorry

/-- The augmentation of the fixed K-injective replacement used by the recorded Hom.
Source: Stacks 079P, 0A95 (blueprint: lem-zl-specified-hom-scalar-evaluation). -/
def specifiedHomResolutionUnit (X : Scheme.{u}) :
    𝟭 (CochainComplex (integralTowerModules l E X) ℤ) ⟶
      coefficientHomResolution.{u, u+1, u} (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) :=
  letI : IsGrothendieckAbelian.{u+1} (integralTowerModules l E X) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1, u, u}
      (Scheme.ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X)).1
  CochainComplex.toKInjectiveResolution.{u+1} _

/-- The actual chain-Hom normalization, including its equality after localization.
The input K-injective I need not be the fixed replacement; the target replacement J
and its augmentation are fixed. Source: blueprint common-stage paragraph, comparison
construction Steps 11--12; Stacks 0A8X, 08J9
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: for each homogeneous Hom section project to its (m,m+r) factor. The formula
q(x)(y) tensor (sb), followed by the fixed augmentation, is balanced and S-linear.
The differential d(h)=d_I h-(-1)^r h d_P makes it a chain map, since scalars have
degree zero. Product projections and sheafified pure tensors prove uniqueness.
Uncurry it on Q tensor P; the result is exactly scalar-extended representative
evaluation. The normalized K-flat tensor models and fixed Hom localization comparison
therefore give the displayed square. For the opposite input order insert (-1)^(mr).
Quasi-isomorphisms q and the K-injective augmentation become invertible, so this
square identifies the same ordinary map on any such representatives. Completion
then uses precisely scalarCompletion on its output and inputs, as in the main theorem. -/
theorem specifiedHomScalarChain (X : Scheme.{u})
    (P I Q : CochainComplex (integralTowerModules l E X) ℤ)
    (_hP : integralOperationsGoodComplex l E X P)
    (_hQ : integralOperationsGoodComplex l E X Q) [I.IsKInjective]
    (_hM : sfIntegralConstructible l E X (DerivedCategory.Q.obj P))
    (_hN : sfIntegralConstructible l E X (DerivedCategory.Q.obj I))
    (q : Q ⟶ homComplex (R := completedIntegralCommRingSheafUnrestricted l E X) P I)
    [QuasiIso q] :
    ∃! δ : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      homComplex (R := completedIntegralCommRingSheafUnrestricted l L X)
        (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P)
        ((coefficientHomResolution.{u, u+1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X)).obj
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)),
      (∀ (r m : ℤ) (U : X.ProEtᵒᵖ) (x : (Q.X r).val.obj U) (y : (P.X m).val.obj U)
        (s b : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U),
        coefficientHomSectionEvaluation.{u, u+1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X) _ _ _ δ r m (m+r) rfl U
          (integralOrdinaryTensorSection l E L ι X (Q.X r) U s x)
          (integralOrdinaryTensorSection l E L ι X (P.X m) U b y) =
        ((((specifiedHomResolutionUnit l L X).app
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)).f
          (m+r)).val.app U)
          (integralOrdinaryTensorSection l E L ι X (I.X (m+r)) U (s*b)
            (((((coefficientHomComponent.{u, u+1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I r m (m+r) rfl).val.app U
                ((q.f r).val.app U x)).app
                  (op (CategoryTheory.Over.mk (𝟙 U.unop)))).hom) y))) ∧
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map δ =
        (integralOrdinaryDerivedScalar l E L ι X).map
          (DerivedCategory.Q.map q ≫
            DerivedCategory.Q.map
              ((homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E X)).obj
                (op P) |>.map ((specifiedHomResolutionUnit l E X).app I)) ≫
            (coefficientHomResolutionIso.{u, u+1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I).inv) ≫
          scalarHomOrdinary l E L ι X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) ≫
          (integralDerivedInternalHom l L X).map (Prod.mkHom
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.inv.app P).op
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app I)) ≫
          (coefficientHomResolutionIso.{u, u+1, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l L X) _ _).hom := by
  sorry

/-- Identity and tower equations after the specified completion identifications.
The unit is ordinary multiplication followed by the canonical completeness unit;
the associator is the one fixed on sheafified pure tensors, not a new choice.
Source: blueprint common-stage paragraph; Stacks 08J9
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: for the identity, uncurry and use scalar multiplication r tensor x ↦ rx.
The quotient-map completion unit, including its zero shifted component, identifies
completed identity extension with the original complete object. For a tower, direct
and successive chain maps evaluate the same Hom section and multiply their degree-zero
coefficients. Associativity gives b(ss')=(bs)s'; the input-first convention gives
(-1)^(degree(m)*degree(h)) on both routes. Localization preserves equality and the
normalized completion maps cancel in the two composites. This is precisely the
Hom clause of scalarOperationsOrdinary_unit/tower with the identified comparison. -/
theorem specifiedHomScalarCoherence (X : Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E X))
    (hM : sfIntegralConstructible l E X M) (hN : sfIntegralConstructible l E X N) :
    ((integralDerivedInternalHom l E X).map (Prod.mkHom
        (((integralOrdinaryDerivedScalarUnit l E X).inv.app M).op) (𝟙 N)) ≫
      (integralOrdinaryDerivedScalarUnit l E X).inv.app
        ((integralDerivedInternalHom l E X).obj (op M, N)) ≫
      specifiedHomIdentified l E E (AlgHom.id ℚ_[l] E) X M N hM.1 hN.1 =
      (integralDerivedInternalHom l E X).map (Prod.mkHom
        (𝟙 (op ((integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) X).obj M)))
        ((integralOrdinaryDerivedScalarUnit l E X).inv.app N))) ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      (j : L →ₐ[ℚ_[l]] F),
      (integralOrdinaryDerivedScalar l L F j X).map
          (specifiedHomIdentified l E L ι X M N hM.1 hN.1) ≫
        scalarHomOrdinary l L F j X
          ((integralOrdinaryDerivedScalar l E L ι X).obj M)
          ((integralOrdinaryDerivedScalar l E L ι X).obj N) ≫
        (integralDerivedInternalHom l F X).map (Prod.mkHom
          (((integralOrdinaryDerivedScalarComp l E L ι X F j).inv.app M).op)
          ((integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
          ((integralDerivedInternalHom l E X).obj (op M, N)) ≫
        specifiedHomIdentified l E F (j.comp ι) X M N hM.1 hN.1) := by
  sorry

/-- Raw rationalization retains the specified comparison and its naturality for
arbitrary localized arrows in both inputs. No restriction to integral lifts or
pure tensors is made. Source: blueprint rational/common-stage paragraphs
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: when the integral Hom is constructible, all completed endpoints lie in the
integral constructible categories. Localize the specific integral map and its inverse,
as in rationalHomScalarComparison_existsUnique. Rational internal Hom is bilinear on
Hom tensor E, with contravariance in its first input. Multiply integral naturality
by each scalar and expand finite sums. This proves naturality for every localized
arrow, including denominators and ramified embeddings. Localization preserves the
identity and tower equations because it preserves composites and inverses. -/
theorem specifiedHomScalarRational (X : Scheme.{u})
    (P P' : (constructibleRationalHomPairs l E X).FullSubcategory)
    (a : P'.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ P'.obj.2) :
    HEq (rationalHomScalarComparison l E L ι X P).hom
      ((sfRationalConstructibleLocalization l L X).map
        (integralHomScalarComparison l E L ι X
          (integralPairOfRationalHomPair l E X P)).hom) ∧
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((rationalDerivedInternalHom l E X).map
          (ObjectProperty.homMk (X := P) (Y := P') (Prod.mkHom a.op b))) ≫
      (rationalHomScalarComparison l E L ι X P').hom =
    (rationalHomScalarComparison l E L ι X P).hom ≫
      (rationalDerivedInternalHom l L X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E L ι X P)
          (Y := rationalHomScalarPair l E L ι X P')
          (Prod.mkHom
            (((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map a).op)
            ((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map b))) := by
  sorry

/-- Identity and tower coherence survive in the raw rationalized categories.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: the integral identified maps satisfy the unit and tower equations by the
representative evaluation calculation. The specified completed associators are their
conjugates by the quotient-completion units. Cancel those units in the integral
squares. Raw scalar localization sends the resulting equations and inverses to the
displayed rational equations. Its objects are unchanged, so constructible integral
Hom is exactly the permitted-pair condition; no Karoubi completion is involved. -/
theorem specifiedHomScalarRationalCoherence (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    ((rationalHomScalarComparison l E E (AlgHom.id ℚ_[l] E) X P).hom ≫
      (rationalDerivedInternalHom l E X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E E (AlgHom.id ℚ_[l] E) X P) (Y := P)
          (Prod.mkHom
            (((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app P.obj.1.unop).op)
            ((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app P.obj.2))) =
      (sfRationalScalarUnit l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalDerivedInternalHom l E X).obj P)) ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      (j : L →ₐ[ℚ_[l]] F),
      (sfRationalScalarExtension l L X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).map
          (rationalHomScalarComparison l E L ι X P).hom ≫
        (rationalHomScalarComparison l L F j X (rationalHomScalarPair l E L ι X P)).hom ≫
        (rationalDerivedInternalHom l F X).map
          (ObjectProperty.homMk
            (X := rationalHomScalarPair l L F j X (rationalHomScalarPair l E L ι X P))
            (Y := rationalHomScalarPair l E F (j.comp ι) X P)
            (Prod.mkHom
              (((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P.obj.1.unop).op)
              ((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app P.obj.2))) =
        (sfRationalScalarComp l E L ι X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
            ((rationalDerivedInternalHom l E X).obj P) ≫
          (rationalHomScalarComparison l E F (j.comp ι) X P).hom) := by
  sorry

/-- The displayed evaluation identity itself in raw rationalization, when its Hom
output is constructible. The right side is the localized conjugate of the ordinary
evaluation-transpose map, using exactly the three canonical completion units.
Source: blueprint rational/common-stage paragraph
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: apply the integral comparison identity, then cancel the invertible Hom-output
completion unit. Lift that equality through the faithful full integral subcategory.
Rational localization preserves the composite, inverses and equality. Its specified
coefficient comparison is the localization of integralHomScalarComparison, giving
this formula for the actual rationalHomScalarComparison, not a newly chosen map. -/
theorem specifiedHomScalarRationalEvaluation (X : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E X).FullSubcategory) :
    (sfRationalConstructibleLocalization l L X).map
      (integralHomScalarComparison l E L ι X P).hom =
    (sfRationalConstructibleLocalization l L X).map
      (ObjectProperty.homMk
        (X := (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj
            ((constructibleIntegralHom l E X).obj P))
        (Y := (constructibleIntegralHom l L X).obj (integralHomScalarPair l E L ι X P))
        ((scalarCompletionIso l E L ι X
          ((integralDerivedInternalHom l E X).obj (op P.obj.1.unop.obj, P.obj.2.obj))
          P.property.1).inv ≫
          scalarHomOrdinary l E L ι X P.obj.1.unop.obj P.obj.2.obj ≫
          (integralDerivedInternalHom l L X).map (Prod.mkHom
            ((scalarCompletionIso l E L ι X P.obj.1.unop.obj P.obj.1.unop.property.1).inv.op)
            ((scalarCompletionIso l E L ι X P.obj.2.obj P.obj.2.property.1).hom)))) := by
  sorry

end WeilConjectures
