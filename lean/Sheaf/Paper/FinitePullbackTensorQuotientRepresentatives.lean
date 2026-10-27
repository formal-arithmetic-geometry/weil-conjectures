/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.CompletedPullbackTowerCore
public import Sheaf.Paper.FinitePullbackTensorConstruction

/-! # Quotient compatibility on flat K-flat tensor representatives

Source: Stacks Tags 06YY and 07A4, the quotient compatibility step of the
completed pullback/tensor comparison.
(blueprint: lem-pur-finite-pullback-tensor-quotient-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  coefficientFiniteQuotientDerived coefficientFiniteQuotientModel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive

/-- The quotient tensor square holds on flat-term K-flat pairs.
Source: Stacks, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product),
with the derived change-of-rings construction of Tag 06YY
(blueprint: lem-pur-finite-pullback-tensor-quotient-representatives).
Proof: use the flat-term K-flat complexes P and Q to compute their derived tensor.
The ordinary unit equation hc identifies the quotient/pullback comparison on every
section inserted by both adjunction units. The degree equations hcc identify its
termwise extension on complexes. On the total summand of bidegree (i,j), both
paths carry 1 tensor f*(x tensor y) to f*(1 tensor x) tensor f*(1 tensor y).
The quotient tensor normalization gives exactly this formula for its tensorator.
Balancing, sheafification, and the total-summand inclusions determine the two
ordinary chain maps, so they agree; the signed differential is the same along
both paths. Apply the derived quotient functor. The normalized square he rewrites
all quotient/pullback components, and the quotient model counits rewrite the
remaining coefficient comparisons. Naturality cancels the intermediate model
isomorphisms, yielding the displayed square. No flatness of the coefficient
quotient is used, and the same calculation includes m=n and zero complexes.
This assertion concerns these representative pairs only; extension to arbitrary
derived objects requires a separate resolution and naturality argument. -/
theorem finitePullbackTensor_quotient_representatives {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (c : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (c.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x))
    (cc : (sfIntrinsicPullback
        (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
      (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ))
    (hcc : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ),
      (cc.hom.app P).f i = c.hom.app (P.X i))
    (good : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E Y m) P →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := integralCoefficientCommRingSheaf l E X m)
        (((sfIntrinsicPullback
          (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ)).obj P))
    (e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f)
    (he : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (good P hP)).hom ≫
          DerivedCategory.Q.map (cc.hom.app P))
    (P Q : CochainComplex (normalizedDVRModules l E Y m) ℤ)
    (hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m) P)
    (hQ : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientFiniteQuotientDerived l E X h).map
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom := by sorry

end WeilConjectures
