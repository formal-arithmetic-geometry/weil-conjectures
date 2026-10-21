/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.CompletionUnitModels
import Sheaf.Paper.CompletionUnitCanonicalModels

/-!
# The actual completion unit on a strict quotient cone

Source: blueprint main-20261015, trace formula, rational Frobenius integral model,
proof (2)--(3); Stacks 07A6, 09T5, 0D6E, 0941 and 08TC. This is the normalization
refinement of those constructions, not a verbatim assertion of a Stacks tag.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

The auxiliary structures package canonical constructions and their normalization
conditions. They introduce no alternative tensor, limit, or derived category.
The theorem asserts their existence together with the whole-morphism unit formula.
The compatible-model construction is isolated in `canonicalModels`; the proof here
derives the cone, unit and two-resolution formulas from its normalizations.
Index n denotes the positive exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures
namespace CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem transpose_natural (M : OrdinaryModel l E W)
    {Q : CochainComplex (scalarReductionSource l E W) ℤ}
    {I : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (a : (M.quotient l E W).obj Q ⟶ I) :
    M.transpose l E W a = M.augmentation l E W Q ≫
      lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((tower l E W).map a)) := by
  dsimp only [OrdinaryModel.transpose, OrdinaryModel.augmentation]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simpa only [Functor.comp_map, Functor.comp_obj, roosLimitFunctor, Category.assoc]
    using congrArg
    (fun f ↦ (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q ≫ f)
    (M.limitComparison.hom.naturality a)

private theorem coneAugmentation_coordinates (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (p : ℤ) :
    (M.coneAugmentation l E W Q).f (p + 1) ≫
        (roosχ ((tower l E W).obj ((M.quotient l E W).obj Q)) p).hom =
      biprod.lift 0
        ((Pi.lift (fun n : ℕ ↦ M.augmentation l E W Q ≫
          limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
            (op n))).f (p + 1)) := by
  dsimp only [OrdinaryModel.coneAugmentation]
  rw [HomologicalComplex.comp_f, Category.assoc, roosι_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp

private theorem limitUnit_isIso
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    IsIso (D.limitUnit.app J) := by
  have hn := D.limitUnit_normalization J
  have : IsIso (D.limitUnit.app J ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom

private theorem roosι_quasiIso
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    QuasiIso (roosι J) := by
  have := limitUnit_isIso l E W D J
  have : IsIso (DerivedCategory.Q.map (roosι J) ≫ D.roos.hom.app J) := by
    rw [D.roos_normalization]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (roosι J)) :=
    IsIso.of_isIso_comp_right _ (D.roos.hom.app J)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp this

private theorem unit_at_complex
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) :
    S.adjunction.unit.app (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
        (D.completionComparison l E W Q hQ hflat).hom := by
  have := D.reduction_isIso Q hQ hflat
  apply (cancel_mono ((coefficientSequenceLimit l E W).map
    (D.reductionComparison.app Q))).1
  have h := D.hom_normalization Q ((M.quotient l E W).obj Q) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_unit] at h
  erw [Category.comp_id, Category.comp_id] at h
  rw [h, D.systemUnit_composition]
  dsimp only [DerivedModel.completionComparison, OrdinaryModel.coneAugmentation,
    OrdinaryModel.augmentation, OrdinaryModel.transpose, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app, asIso_inv]
  simp only [Category.assoc]
  simp only [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← D.roos_normalization]
  simp only [Category.assoc]


private theorem unit_at_representative
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite)
    (N : DerivedCategory (scalarReductionSource l E W))
    (q : DerivedCategory.Q.obj Q ≅ N) :
    S.adjunction.unit.app N = q.inv ≫
      DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
      (D.completionComparison l E W Q hQ hflat).hom ≫
      (coefficientSequenceLimit l E W).map (S.reduction.map q.hom) := by
  apply (cancel_epi q.hom).1
  have hn := S.adjunction.unit.naturality q.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [hn]
  rw [unit_at_complex l E W D Q hQ hflat]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem augmentation_sections (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (p : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ) (x : (Q.X p).val.obj V) :
    (((M.augmentation l E W Q ≫
        limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
          (op n)).f p ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          (((M.quotient l E W).obj Q).X p) ≫
        (scalarReductionRestriction l E W n).map
          ((M.evaluation n).hom.app (Q.X p))).val.app V) x =
      unrestrictedIntegralTensorSection l E W n (Q.X p) V 1 x := by
  have hu : (M.augmentation l E W Q).f p =
      M.adjunction.unit.app (Q.X p) ≫
        (M.limitComparison.hom.app ((M.quotient l E W).obj Q)).f p := by
    dsimp only [OrdinaryModel.augmentation, OrdinaryModel.transpose]
    rw [Adjunction.homEquiv_unit]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, Adjunction.mapHomologicalComplex_unit_app_f]
    erw [Category.comp_id]
  have hp := M.limitComparison_projection ((M.quotient l E W).obj Q) n p
  rw [HomologicalComplex.comp_f] at hp
  have hproj : (M.augmentation l E W Q ≫
      limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n)).f p =
      M.adjunction.unit.app (Q.X p) ≫ limit.π
        ((coefficientSequenceRestriction l E W).obj
          (((M.quotient l E W).obj Q).X p)) (op n) := by
    rw [HomologicalComplex.comp_f, hu, Category.assoc, hp]
  rw [hproj]
  exact M.unit_tensor (Q.X p) n V x

private theorem limit_resolution_compatibility
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : (tower l E W).obj I ⟶ J) [QuasiIso j] :
    DerivedCategory.Q.map
        (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
        (D.limitUnit.app J ≫
          (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
          (coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I)) =
      DerivedCategory.Q.map (M.limitComparison.inv.app I) ≫ D.systemUnit.app I := by
  have hn := D.limitUnit.naturality j
  dsimp only [Functor.comp_map] at hn
  change DerivedCategory.Q.map (roosLimitFunctor.map j) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rw [D.systemUnit_composition]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  change _ = (DerivedCategory.Q.map (𝟙 _) ≫ _) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem limit_resolution_quasiIso
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (tower l E W).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) := by
  have := limitUnit_isIso l E W D J
  have := D.system_isIso I inferInstance
  have : IsIso (DerivedCategory.Q.map
      (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
      (D.limitUnit.app J ≫
        (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I))) := by
    rw [limit_resolution_compatibility l E W D I J j]
    infer_instance
  have : IsIso (DerivedCategory.Q.map
      (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j))) :=
    IsIso.of_isIso_comp_right _
      (D.limitUnit.app J ≫
        (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp this

private theorem transpose_cone_natural (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj Q ⟶ I)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : (tower l E W).obj I ⟶ J) :
    (M.transpose l E W a ≫
        lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
        roosι J =
      M.coneAugmentation l E W Q ≫ roosF.map ((tower l E W).map a ≫ j) := by
  rw [transpose_natural l E W M a]
  dsimp only [OrdinaryModel.coneAugmentation]
  simp only [Functor.map_comp, Category.assoc]
  have h := roosι_natural ((tower l E W).map a)
  rw [roosι_natural j]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ M.augmentation l E W Q ≫ f ≫ roosF.map j) h

private theorem comparison_resolution
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj Q ⟶ I)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (tower l E W).obj I ⟶ J) [QuasiIso j]
    (eCone : DerivedCategory.Q.obj (limit J.asFunctor) ≅
      DerivedCategory.Q.obj (roosF.obj J))
    (heCone : eCone.hom = DerivedCategory.Q.map (roosι J)) :
    (D.completionComparison l E W Q hQ hflat).hom ≫
        (coefficientSequenceLimit l E W).map (D.reductionComparison.app Q) ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a) =
      DerivedCategory.Q.map (roosF.map ((tower l E W).map a ≫ j)) ≫
        eCone.inv ≫
        D.limitUnit.app J ≫
        (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I) := by
  have := D.reduction_isIso Q hQ hflat
  rw [← D.roos_normalization J, ← heCone]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hn := D.roos.hom.naturality ((tower l E W).map a ≫ j)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  dsimp only [DerivedModel.completionComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  erw [Category.id_comp]
  congr 1
  have hf := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.naturality a
  dsimp only [Functor.comp_map] at hf
  dsimp only [coefficientSequenceLimit, coefficientSequenceDerivedRestriction,
    Functor.comp_map]
  simpa only [Functor.map_comp, Functor.comp_obj, tower, Iso.app] using
    congrArg (coefficientConstantTowerLimit l E W).map hf.symm

/-- The actual completion unit, including its two-resolution composition normalization.
The existential packages choose only the canonical tensor/derived constructions fixed
by their universal properties and displayed normalizations. They add no hypothesis on N.
Every resolution in the last clause is universally quantified.

Source: blueprint main-20261015, rational Frobenius integral model, proof (2)--(3),
normalization refinement; Stacks 07A6, 09T5, 0D6E, 0941, 08TC.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

Proof:
1. Take the compatible ordinary and derived models from canonicalModels. Its
   construction is the separate lemma realizing the original proof steps 1--4.
2. Express the ordinary transpose by its adjunction unit. Naturality of the
   termwise-limit comparison identifies it with augmentation followed by limit(a).
   The specified limit projections and unit_tensor give the local tensor formula.
3. Compose augmentation with the strict Roos inclusion. The inclusion's coordinate
   equation gives the zero shifted coordinate, and its naturality proves the
   strict equality between the resolved transpose and the image of augmentation.
4. Apply hom_normalization to the identity of the quotient complex. Cancel the
   invertible reduction comparison and use systemUnit_composition and
   roos_normalization. This identifies the actual adjunction unit as a whole
   morphism. Naturality transports it along every representative isomorphism q.
5. The K-injective normalization makes limitUnit invertible. Together with the
   invertible systemUnit and naturality of limitUnit, it makes limit(j) invertible
   after localization, hence a quasi-isomorphism. The Roos normalization likewise
   makes the inclusion at J a quasi-isomorphism. These give eI, eJ and eCone with
   exactly the specified maps. Naturality of the Roos comparison and the exact
   restriction localization comparison gives the resolved comparison formula.
6. Substitute the strict equality from step 3 in the whole-unit equation and cancel
   the reduction comparison, the resolution a and eCone. This gives the formula
   for every pair of resolutions. Finally use naturality of the actual unit for
   every derived morphism. No detection by finite projections, completeness,
   boundedness or preservation of K-injectivity by restriction is used. -/
theorem completionUnitStrictQuotientModel
    [∀ x : W, Invertible (l : W.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S)
      (M : OrdinaryModel l E W) (D : DerivedModel l E W S M),
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite),
        (∀ (p : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ) (x : (Q.X p).val.obj V),
          (((M.augmentation l E W Q ≫
              limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
                (op n)).f p ≫
              (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
                (((M.quotient l E W).obj Q).X p) ≫
              (scalarReductionRestriction l E W n).map
                ((M.evaluation n).hom.app (Q.X p))).val.app V) x =
            unrestrictedIntegralTensorSection l E W n (Q.X p) V 1 x) ∧
        (∀ p : ℤ,
          (M.coneAugmentation l E W Q).f (p + 1) ≫
              (roosχ ((tower l E W).obj ((M.quotient l E W).obj Q)) p).hom =
            biprod.lift 0
              ((Pi.lift (fun n : ℕ ↦ M.augmentation l E W Q ≫
                limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
                  (op n))).f (p + 1))) ∧
        (∀ (N : DerivedCategory (scalarReductionSource l E W))
          (q : DerivedCategory.Q.obj Q ≅ N),
          S.adjunction.unit.app N = q.inv ≫
            DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
            (D.completionComparison l E W Q hQ hflat).hom ≫
            (coefficientSequenceLimit l E W).map (S.reduction.map q.hom)) ∧
        (∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
          (a : (M.quotient l E W).obj Q ⟶ I) [QuasiIso a] [I.IsKInjective]
          (_hI : ∀ p : ℤ, Injective (I.X p))
          (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
          (j : (tower l E W).obj I ⟶ J) [QuasiIso j] [J.IsKInjective]
          (_hJ : ∀ p : ℤ, Injective (J.X p)),
          ∃ (eI : DerivedCategory.Q.obj (limit ((tower l E W).obj I).asFunctor) ≅
              (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I))
            (eJ : DerivedCategory.Q.obj (limit J.asFunctor) ≅
              (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I))
            (eCone : DerivedCategory.Q.obj (limit J.asFunctor) ≅
              DerivedCategory.Q.obj (roosF.obj J)),
            eCone.hom = DerivedCategory.Q.map (roosι J) ∧
            eI.hom = DerivedCategory.Q.map (M.limitComparison.inv.app I) ≫
              D.systemUnit.app I ∧
            eJ.hom = D.limitUnit.app J ≫
              (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
              (coefficientConstantTowerLimit l E W).map
                ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I) ∧
            QuasiIso (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ∧
            QuasiIso (roosι J) ∧
            DerivedCategory.Q.map
                (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                eJ.hom = eI.hom ∧
            M.transpose l E W a = M.augmentation l E W Q ≫
              lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
                ((tower l E W).map a)) ∧
            (M.transpose l E W a ≫
                lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                roosι J =
              M.coneAugmentation l E W Q ≫ roosF.map ((tower l E W).map a ≫ j) ∧
            (D.completionComparison l E W Q hQ hflat).hom ≫
                (coefficientSequenceLimit l E W).map (D.reductionComparison.app Q) ≫
                (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a) =
              DerivedCategory.Q.map (roosF.map ((tower l E W).map a ≫ j)) ≫
                eCone.inv ≫ eJ.hom ∧
            (∀ (N : DerivedCategory (scalarReductionSource l E W))
              (q : DerivedCategory.Q.obj Q ≅ N),
              S.adjunction.unit.app N = q.inv ≫
                DerivedCategory.Q.map (M.transpose l E W a ≫
                  lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                eJ.hom ≫
                (coefficientSequenceLimit l E W).map (inv (DerivedCategory.Q.map a)) ≫
                (coefficientSequenceLimit l E W).map
                  (@asIso _ _ _ _ (D.reductionComparison.app Q)
                    (D.reduction_isIso Q hQ hflat)).inv ≫
                (coefficientSequenceLimit l E W).map (S.reduction.map q.hom)))) ∧
      (∀ (N N' : DerivedCategory (scalarReductionSource l E W)) (h : N ⟶ N'),
        h ≫ S.adjunction.unit.app N' = S.adjunction.unit.app N ≫
          (coefficientSequenceLimit l E W).map (S.reduction.map h)) := by
  obtain ⟨S, coherence, M, ⟨D⟩⟩ := canonicalModels l E W
  refine ⟨S, coherence, M, D, ?_, ?_⟩
  · intro Q hQ hflat
    refine ⟨augmentation_sections l E W M Q, coneAugmentation_coordinates l E W M Q,
      unit_at_representative l E W D Q hQ hflat, ?_⟩
    intro I a _ _ _hI J j _ _ _hJ
    have := D.system_isIso I inferInstance
    have := limitUnit_isIso l E W D J
    have hι := roosι_quasiIso l E W D J
    have : IsIso (DerivedCategory.Q.map (roosι J)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hι
    let eI : DerivedCategory.Q.obj (limit ((tower l E W).obj I).asFunctor) ≅
        (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I) :=
      asIso (DerivedCategory.Q.map (M.limitComparison.inv.app I) ≫ D.systemUnit.app I)
    let eJ : DerivedCategory.Q.obj (limit J.asFunctor) ≅
        (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I) :=
      asIso (D.limitUnit.app J ≫
        (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I))
    let eCone : DerivedCategory.Q.obj (limit J.asFunctor) ≅
        DerivedCategory.Q.obj (roosF.obj J) := asIso (DerivedCategory.Q.map (roosι J))
    have hc : (D.completionComparison l E W Q hQ hflat).hom ≫
        (coefficientSequenceLimit l E W).map (D.reductionComparison.app Q) ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a) =
      DerivedCategory.Q.map (roosF.map ((tower l E W).map a ≫ j)) ≫
        eCone.inv ≫ eJ.hom := by
      simpa only [eJ, eCone, asIso_hom, asIso_inv, Category.assoc] using
        comparison_resolution l E W D Q hQ hflat I a J j eCone rfl
    have ht := transpose_cone_natural l E W M Q I a J j
    refine ⟨eI, eJ, eCone, rfl, rfl, rfl,
      limit_resolution_quasiIso l E W D I J j, hι,
      limit_resolution_compatibility l E W D I J j,
      transpose_natural l E W M a, ht, hc, ?_⟩
    intro N q
    rw [unit_at_representative l E W D Q hQ hflat N q]
    have := D.reduction_isIso Q hQ hflat
    have hu : DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
        (D.completionComparison l E W Q hQ hflat).hom =
      DerivedCategory.Q.map (M.transpose l E W a ≫
        lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
        eJ.hom ≫
        (coefficientSequenceLimit l E W).map (inv (DerivedCategory.Q.map a)) ≫
        (coefficientSequenceLimit l E W).map
          (@asIso _ _ _ _ (D.reductionComparison.app Q)
            (D.reduction_isIso Q hQ hflat)).inv := by
      apply (cancel_mono ((coefficientSequenceLimit l E W).map
        (D.reductionComparison.app Q))).1
      apply (cancel_mono ((coefficientSequenceLimit l E W).map
        (DerivedCategory.Q.map a))).1
      simp only [Category.assoc, ← Functor.map_comp, asIso_inv, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
      simp only [Functor.map_comp, Category.comp_id, Category.assoc]
      rw [hc]
      have ht' := congrArg DerivedCategory.Q.map ht
      simp only [Functor.map_comp, Category.assoc] at ht'
      have he : DerivedCategory.Q.map (M.transpose l E W a ≫
          lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) =
        DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
          DerivedCategory.Q.map (roosF.map ((tower l E W).map a ≫ j)) ≫
          eCone.inv := by
        apply (cancel_mono eCone.hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        simpa only [eCone, asIso_hom, Functor.map_comp, Category.assoc] using ht'
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f ↦ f ≫ eJ.hom) he.symm
    simpa only [Category.assoc] using congrArg
      (fun f ↦ q.inv ≫ f ≫
        (coefficientSequenceLimit l E W).map (S.reduction.map q.hom)) hu
  · intro N N' h
    exact S.adjunction.unit.naturality h

end CompletionUnit
end WeilConjectures
