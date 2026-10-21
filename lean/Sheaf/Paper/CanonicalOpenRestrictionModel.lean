/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Canonical open restriction on augmented quotient models

Source: Stacks Project, Tags 0E8I, 0GL1, 03DJ, 06YY and 0941.
This isolates the representative construction, independently of reconstruction or
realization through total limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (SX : CoefficientDerivedSystemCalculus l E X)

/-- The open-adjunction mate of the inverse extension comparison is invertible and
has one simultaneous augmented restriction model.
Source: Stacks sites-modules.tex, Tags 03DJ and 0E8I; sites-cohomology.tex,
Tags 0GL1, 0G7E and 0941; steps 2--4 of the adjunction transport argument.
(blueprint: lem-sf-canonical-open-restriction-model).

Proof: restrict one flat-term K-flat representative and each of its quotient tensors
on the localized site. Restriction commutes with tensor by the identity on the
sectionwise pure tensors. The quotient maps and scalar-unit maps therefore commute
before sheafification and in every degree. The fixed coefficient equivalences
transport these maps to U, using their actual units and counits. They form an
isomorphism of strict systems, not just a family of derived evaluations. Localize
on the resolving class to obtain a natural comparison. On an extension summand,
the adjunct of its component sends [x] tensor a to x tensor a; this is also the
inverse supplied extension comparison followed by the ordinary counit. The
normalized strict extension models in the hypothesis identify these maps before
localization. The termwise open adjunction then identifies the localized comparison
with mateEquiv applied to r inverse. Naturality removes the representative choices.
Its good restricted representative, augmented presentations and chain comparison
are precisely the witnesses in the conclusion. No completeness hypothesis enters. -/
theorem canonicalOpenRestrictionModel
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (tensor : TensorComparison l E j o)
    (hr :
      ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q),
    ∃ (hJQ : integralOperationsGoodComplex l E X
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (D : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (eC : SU.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (eD : SX.reduction.obj (DerivedCategory.Q.obj
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
            (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : D ≅ ((systemExtension l E j o).mapHomologicalComplex (.up ℤ)).obj C),
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        Q hQ.1 C eC κC ∧
      AugmentedPresentation l E U SU Q C eC κC ∧
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hJQ.1 D eD κD ∧
      AugmentedPresentation l E X SX
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) D eD κD ∧
      (r.hom.app (DerivedCategory.Q.obj Q) ≫ (J l E j o).map eC.hom ≫
        (systemExtension l E j o).mapDerivedCategoryFactors.hom.app C =
      SX.reduction.map ((extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eD.hom ≫ DerivedCategory.Q.map f.hom) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E X n).map (f.hom.f i) ≫
          (extensionEvaluation l E j o n).hom.app (C.X i) ≫
          (finiteExtension l E j o n).map ((κC n).hom.f i) =
        (κD n).hom.f i ≫ (tensor.ordinary n).hom.app (Q.X i))) :
    ∃ s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o,
      s.hom = (mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
        (TwoSquare.mk _ _ _ _ r.inv)).natTrans ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E X Q),
    ∃ (hRes : integralOperationsGoodComplex l E U
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (CX : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (CU : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (eX : SX.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj CX)
      (eU : SU.reduction.obj (DerivedCategory.Q.obj
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj CU)
      (κX : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj CX ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κU : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj CU ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj
            (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : CU ≅ ((systemRestriction l E j o).mapHomologicalComplex (.up ℤ)).obj CX),
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        Q hQ.1 CX eX κX ∧
      AugmentedPresentation l E X SX Q CX eX κX ∧
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hRes.1 CU eU κU ∧
      AugmentedPresentation l E U SU
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) CU eU κU ∧
      (SU.reduction.map ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eU.hom ≫ DerivedCategory.Q.map f.hom =
      s.hom.app (DerivedCategory.Q.obj Q) ≫ (P l E j o).map eX.hom ≫
        (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app CX) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E U n).map (f.hom.f i) ≫
          ((o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj (CX.X i))).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso ((o.openSystems.restrictionEvaluation n).app (CX.X i))).hom ≫
          (finiteRestriction l E j o n).map ((κX n).hom.f i) =
        (κU n).hom.f i ≫ (((o.finite n).toAdjunction.comp
          (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
            (rings l E X n) (openObject j))).unit.app _ ≫
    (finiteRestriction l E j o n).map
      ((tensor.ordinary n).inv.app ((restriction l E j o).obj (Q.X i))) ≫
    (finiteRestriction l E j o n).map
      ((scalarReductionExtension l E X n).map
        ((ordinaryAdjunction l E j o).counit.app (Q.X i)))))) := by sorry

end WeilConjectures.CanonicalOpenRestriction
