/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.CoefficientTensorCurryNormalization
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Unsigned ordinary evaluation and its derived localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A98 and Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization).

The formulas use the recorded sheafified tensor generators, Hom-product projections,
coefficient-unit identifications, and fixed K-injective augmentation. The ordinary map
exists for arbitrary complexes; only its derived comparison requires the stated K-flatness
and augmentation quasi-isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Evaluate the actual Hom-product projection at the identity of the localized site.
Source: Stacks Section 0A8X, Tag 08JE
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryHomValue
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (n a b : ℤ) (h : a + n = b) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E F).X n).val.obj U) (x : (E.X a).val.obj U) :
    (F.X b).val.obj U :=
  coefficientHomSectionApply.{u, c, v} J R (E.X a) (F.X b) U
    ((coefficientHomComponent.{u, c, v} J R E F n a b h).val.app U φ) x

/-- Extract the coefficient from the supported component of the ordinary dual.
Both transports are the actual degree-zero coefficient-unit identifications.
Source: Stacks Section 0A8X, Tag 08JE
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryDualValue
    (E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (q a : ℤ) (h : a + q = 0) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj U)
    (x : (E.X a).val.obj U) : R.obj.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))).hom.val.app U)
    (ringedOrdinaryHomValue.{c, v, u} J R E (ringedTensorUnitComplex.{c, v, u} J R)
      q a 0 h U φ x)

/-- The unsigned formula on every sheafified tensor generator and Hom projection.
Supported components act by the actual coefficient scalar; all other components vanish.
The equality `hp` only transports between equal integer degrees.
Source: Stacks Tag 08JE, Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def RingedOrdinaryEvaluationFormula
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (aEF : (coefficientTotalTensor.{u, c, v} J R).obj
      (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
        homComplex (R := R) E F) : Prop :=
  ∀ (p q n a b : ℤ) (hn : p + q = n) (hb : a + n = b) (U : Cᵒᵖ)
    (y : (F.X p).val.obj U)
    (φ : ((homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj U)
    (x : (E.X a).val.obj U),
    (∀ (h : a + q = 0) (hp : p = b),
      ringedOrdinaryHomValue.{c, v, u} J R E F n a b hb U
        ((aEF.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hn U y φ)) x =
      (eqToHom (congrArg F.X hp)).val.app U
        (ringedOrdinaryDualValue.{c, v, u} J R E q a h U φ x • y)) ∧
    (a + q ≠ 0 →
      ringedOrdinaryHomValue.{c, v, u} J R E F n a b hb U
        ((aEF.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          p q n hn U y φ)) x = 0)

/-- Apply ordinary Hom to the fixed augmentation already used to define derived Hom.
Source: Stacks Tags 0A95 and 08J9
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedHomAugmentationMap
    (E G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    homComplex (R := R) E G ⟶
      homComplex (R := R) E ((coefficientHomResolution.{u, c, v} J R).obj G) :=
  (homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op E) |>.map
    ((coefficientHomAugmentation.{u, c, v} J R).app G)

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The comparison induced by the fixed augmentation and localization factorization.
Source: Stacks Tags 0A95 and 08J9
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedOrdinaryHomComparison
    (E G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) E G) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj G) :=
  DerivedCategory.Q.map (ringedHomAugmentationMap.{c, v, u} J R E G) ≫
    (coefficientHomResolutionIso.{u, c, v, w} J R E G).inv

/-- The transpose of reassociation, coefficient evaluation and the right unit action.
The coefficient object is identified with the monoidal unit by the recorded coherence.
Source: Stacks Tags 08JD, 08JE and 0A98
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization). -/
def ringedDualTensorHom
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
    (A B : DerivedCategory (RingedTensorModules.{c, v, u} J R)) :
    S.tensor.obj (B, (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
      (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op A, B) :=
  S.transpose _ A B
    ((S.monoidal.associator B
      ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op A, DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) A).hom ≫
      (@MonoidalCategory.tensorLeft _ _ S.monoidal B).map (S.evaluation A
        (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ≫
      (@MonoidalCategory.tensorLeft _ _ S.monoidal B).map unitIso.inv ≫
      (S.monoidal.rightUnitor B).hom)

/-- The ordinary unsigned evaluation exists uniquely and represents derived evaluation
through precisely the two fixed augmentation comparisons.

Source: Stacks Tags 08JD/08JE, 0A98, 08J9 and Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization).

Proof plan (the node's nine steps):
1. On each localized site form the bilinear map (y, phi) ↦ (x ↦ y phi(x)), zero
   outside a+q=0. The presheaf tensor universal property and sheafification factorization
   give the summand maps; Hom products and total coproducts assemble them uniquely.
2. The Hom differential is d_F f - (-1)^(p+q) f d_E. Since d_O=0, applying the
   total differential gives exactly d_F(y) phi(x) - (-1)^(p+q) y phi(d_E x).
   Include the adjacent case a+q+1=0. Generator detection proves the chain equation.
3. Choose a flat-term K-flat resolution s:L→E by lem-pc-kflat-resolution. The fixed
   model makes T=Tot(F tensor D), W=Tot(D tensor L), and O K-flat. No flat-term
   assumption is made on F or D.
4. Precompose each fixed augmentation comparison with H(Qs,1); functoriality identifies
   this with Q Hom(s,I(G)) Hom(E,eta_G) and the fixed Hom comparison, for G=O,F.
   These maps are invertible by the two hypotheses and invertibility of Qs.
5. Define v_s:W→O by phi tensor z ↦ phi(sz). Its chain equation follows from that of s.
   The fixed uncurrying model identifies the inverse transpose of the O comparison
   with Q(v_s) mu_(D,L)^(-1), after cancellation of Q(eta_O).
6. Uncurry the F comparison composed with Q(a). Its representative b sends
   (y tensor phi) tensor z to eta_F(y phi(sz)), by the fixed uncurrying model.
7. Ordinary reassociation followed by 1 tensor v_s and the unit action gives c.
   Both b and eta_F c have the same generators, hence agree. Cancel Q(eta_F).
8. Naturality of the adjunction identifies the other inverse transpose with
   rho (1 tensor Q(v_s) mu_(D,L)^(-1)) alpha (mu_(F,D) tensor 1).
   The induced associator, naturality and right-unit constraints reduce it to
   Q(c) mu_(T,L)^(-1), the expression from step 7.
9. Injectivity of closed transposition and cancellation of H(Qs,1) give the stated
   square. Only F and D are assumed K-flat; only the two Hom augmentation maps
   are assumed quasi-isomorphisms. E need not be K-flat and F need not be K-injective. -/
theorem ringedOrdinaryEvaluation_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃ aEF : (coefficientTotalTensor.{u, c, v} J R).obj
        (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
          homComplex (R := R) E F,
      RingedOrdinaryEvaluationFormula.{c, v, u} J R E F aEF ∧
      (∀ bEF, RingedOrdinaryEvaluationFormula.{c, v, u} J R E F bEF → bEF = aEF) ∧
      ∀ (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
        (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) →
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E F) →
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E F) ∧
        (T.iso J R S F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) hF hD).hom ≫
          S.tensor.map (𝟙 (DerivedCategory.Q.obj F),
            ringedOrdinaryHomComparison.{c, v, u, w} J R E
              (ringedTensorUnitComplex.{c, v, u} J R)) ≫
          ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
            (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map aEF ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F := by
  sorry

end CategoryTheory
