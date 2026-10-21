/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Sheaf.Paper.WitnessCompatibility

/-!
# Bounded acyclic flat models for the proper coefficient map

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings (blueprint:
lem-sp-acyclic-flat-proper-coefficient-model).

The scalar extension, its pullback comparison, and the coefficient mate are the
canonical constructions already provided by the étale six-functor interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/- The three names below expose the canonical objects named in the statement. -/

/-- The derived tensor `T_T = - ⊗ᴸ_{A_T} B_T` used in the coefficient comparison.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The canonical tensor/pullback comparison `λ : T_W r_A^* ≅ r_B^* T_V` for the
coefficient extension; `scalarPullbackIso` is its inverse, used in the transpose below.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientPullbackComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  (scalarPullbackIso φ r).symm

/-- The canonical coefficient map `q_r`, defined as the adjoint mate of the
scalar-extended counit through the comparison above.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  scalarMate φ r

/-- The termwise scalar extension `C_B` of a cochain complex on `W`.
Source: Stacks 0GL6 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
abbrev coefficientExtendedComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
  ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj C

/-- The canonical acyclic-complex comparison, including the homotopy quotient factor.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  DerivedCategory.Qh.map
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)

/-- The ordinary B-linear projection map: the mate of scalar extension of the A-counit
through the ordinary scalar/pullback isomorphism. Its degreewise adjunct is precisely
pullback/tensor reassociation followed by counit tensor identity.
Source: Stacks 0GL6, 07A4 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properSheafCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)).natTrans

/-- The termwise projection chain map pi_C. Mapping the ordinary natural transformation
on complexes guarantees that its components commute with the differentials.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (lowerStar (ModuleCat.{u + 1} A) r ⋙
        ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app C ≫
    (NatTrans.mapHomologicalComplex (properSheafCoefficientMap φ r) (.up ℤ)).app C ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ W ⋙
        lowerStar (ModuleCat.{u + 1} B) r)) (.up ℤ)).inv.app C

/-- The bounded, termwise flat and direct-image-acyclic hypotheses for this model.
Flatness of a term is exactness of tensoring with it (Stacks 03ER), the predicate
`exactFunctor` on the sheaf `tensorRight` recorded for this encoding by def-pc-flat-sheaf-modules.
Both coefficient rings and the proper Noetherian morphism are bound by the theorem.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def IsAcyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n)) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (C.X n))) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight
      ((lowerStar (ModuleCat.{u + 1} A) r).obj (C.X n)))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (C.X n))))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((coefficientExtendedComplex φ W C).X n)))))

section ProofCalculations

section CachedInstances
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
private abbrev cachedPreadditive :
    MonoidalPreadditive (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedCoproducts :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedColimits :
    HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedFlatResolution : Abelian.HasFunctorialFlatResolution
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedInjectiveResolution : Abelian.HasKInjectiveResolutions
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedExactColimits :
    HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedTensor4 : ∀ (X₁ X₂ X₃ X₄ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private abbrev cachedTensor12 : ∀ (X₁ X₂ X₃ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private abbrev cachedTensor23 : ∀ (X₁ X₂ X₃ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private abbrev cachedTensorLeft : ∀ (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
    PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj X) :=
  inferInstance
private abbrev cachedTensorRight : ∀ (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
    PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj X) :=
  inferInstance
end CachedInstances
attribute [local instance] cachedPreadditive cachedCoproducts cachedColimits
  cachedFlatResolution cachedInjectiveResolution cachedExactColimits cachedTensor4
  cachedTensor12 cachedTensor23 cachedTensorLeft cachedTensorRight

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma bounded_flat_kFlat
    {D : Type*} [Category D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [BraidedCategory D] [HasCountableCoproducts D]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (C : CochainComplex D ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n))
    (hf : ∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (C.X n))) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C := by
  obtain ⟨a, b, hb⟩ := hb
  have : C.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun n hn ↦ hb n (Or.inr hn))
  have : C.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun n hn ↦ hb n (Or.inl hn))
  apply CochainComplex.kFlat_of_bounded_of_flat C a b
  intro n
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (C.X n)).symm (hf n), hf n⟩

private lemma bounded_flat_sheaf_kFlat
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (C : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n))
    (hf : ∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (C.X n))) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C := by
  exact bounded_flat_kFlat C hb hf

private def acyclicComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ)) F.rightDerivedFunctorUnit

private lemma acyclicUnit_isIso
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [EnoughInjectives D]
    [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F]
    (C : CochainComplex D ℤ) (a : ℤ) [C.IsStrictlyGE a]
    (hC : ∀ n, F.rightAcyclic (C.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj C)) := by
  let L : CochainComplex.Plus D := ⟨C, a, inferInstance⟩
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient D).obj L)) :=
    F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hC
  have hf : F.rightDerivedFunctorPlusιUnit ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        F.rightDerivedFunctorPlusCompatibility.hom = F.ιRightDerivedFunctorUnit := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h := NatTrans.congr_app hf ((HomotopyCategory.Plus.quotient D).obj L)
  change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj L)) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient D).obj L)) =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj C) at h
  have : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj C)) := by
    rw [← h]
    infer_instance
  infer_instance

private lemma properAcyclicComparison_isIso
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : ℤ) [C.IsStrictlyGE a]
    (hC : ∀ (n : ℤ) (q : ℕ), 0 < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj
          ((DerivedCategory.singleFunctor
            (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (C.X n))))) :
    IsIso (properAcyclicComparison A r C) := by
  have : IsIso ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := by
    apply acyclicUnit_isIso (lowerStar (ModuleCat.{u + 1} A) r) C a
    intro n q
    exact IsZero.of_iso (hC n (q + 1) (Nat.succ_pos q))
      ((lowerStar (ModuleCat.{u + 1} A) r).homologyRightDerivedFunctorObjSingleFunctorIso
        (C.X n) (q + 1)).symm
  unfold properAcyclicComparison
  infer_instance

private def leftComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] {L : DerivedCategory D ⥤ DerivedCategory E}
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) α ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh

section DerivedComparison
variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

private lemma derived_counit_normalization (adj : F ⊣ G) (C : CochainComplex E ℤ) :
    F.leftDerivedFunctor.map ((acyclicComparisonTransformation G).app C) ≫
        adj.derivedAdjunction.counit.app (DerivedCategory.Q.obj C) =
      (leftComparisonTransformation F F.leftDerivedFunctorCounit).app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app C) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  dsimp only [acyclicComparisonTransformation, leftComparisonTransformation,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact h

private lemma derived_unit_normalization (adj : F ⊣ G) (C : CochainComplex D ℤ) :
    adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj C) ≫
        G.rightDerivedFunctor.map
          ((leftComparisonTransformation F F.leftDerivedFunctorCounit).app C) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) ≫
        (acyclicComparisonTransformation G).app
          ((F.mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  dsimp only [acyclicComparisonTransformation, leftComparisonTransformation,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact h
end DerivedComparison

private def transposeTransformation
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : D ⥤ H} {R : H ⥤ D} (adj : L ⊣ R)
    {F : C ⥤ D} {G : C ⥤ H} (η : F ⟶ G ⋙ R) : F ⋙ L ⟶ G where
  app X := (adj.homEquiv _ _).symm (η.app X)
  naturality X Y h := adj.homEquiv_naturality_right_square
    (F.map h) (η.app Y) (η.app X) (G.map h) (η.naturality h)

private def ordinaryScalarRepresentative
    {D E H K : Type*} [Category D] [Category E] [Category H] [Category K]
    [Preadditive D] [Preadditive E] {F : D ⥤ E} {G : E ⥤ D}
    [F.Additive] [G.Additive] (adj : F ⊣ G)
    (Q : CochainComplex D ℤ ⥤ H) (Q' : CochainComplex E ℤ ⥤ K)
    {L : H ⥤ K} {R : K ⥤ H} (ad : L ⊣ R)
    (e : Q' ⋙ R ≅ G.mapHomologicalComplex (.up ℤ) ⋙ Q) :
    Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ Q' :=
  transposeTransformation ad
    (Functor.whiskerRight
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
        NatTrans.mapHomologicalComplex adj.unit (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv) Q ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) e.inv)

private def complexLocalization
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      DerivedCategoryModule A T :=
  DerivedCategory.Q

private def scalarRepresentativeTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    complexLocalization A T ⋙ scalarExtension φ T ⟶
      (ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
        complexLocalization B T :=
  ordinaryScalarRepresentative (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (complexLocalization A T) (complexLocalization B T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors

private def complexTransformation
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (I : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (τ : F ⋙ G ⟶ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex τ (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv

private def coefficientComplexTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  complexTransformation (lowerStar (ModuleCat.{u + 1} A) r)
    (ProEtale.etaleSheafExtendScalars φ V) (ProEtale.etaleSheafExtendScalars φ W)
    (lowerStar (ModuleCat.{u + 1} B) r) (properSheafCoefficientMap φ r)

private lemma mate_component
    {D₁ D₂ D₃ D₄ : Type*}
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {G₁ : D₁ ⥤ D₂} {F₁ : D₂ ⥤ D₁} {G₂ : D₃ ⥤ D₄} {F₂ : D₄ ⥤ D₃}
    {H₁ : D₁ ⥤ D₃} {H₂ : D₂ ⥤ D₄}
    (ad₁ : G₁ ⊣ F₁) (ad₂ : G₂ ⊣ F₂)
    (θ : TwoSquare H₁ G₁ G₂ H₂) (X : D₂) :
    (mateEquiv ad₁ ad₂ θ).natTrans.app X =
      ad₂.unit.app (H₁.obj (F₁.obj X)) ≫
        F₂.map (θ.natTrans.app (F₁.obj X) ≫ H₂.map (ad₁.counit.app X)) := by
  simp only [CategoryTheory.Functor.map_comp]
  simp [mateEquiv_apply]

private theorem mate_comparison
    {D₁ D₂ D₃ D₄ : Type*}
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {G₁ : D₁ ⥤ D₂} {F₁ : D₂ ⥤ D₁} {G₂ : D₃ ⥤ D₄} {F₂ : D₄ ⥤ D₃}
    {H₁ : D₁ ⥤ D₃} {H₂ : D₂ ⥤ D₄}
    (ad₁ : G₁ ⊣ F₁) (ad₂ : G₂ ⊣ F₂)
    (θ : TwoSquare H₁ G₁ G₂ H₂)
    {X U : D₂} {P : D₁} {Y N T : D₃} {J U' Z : D₄}
    (p : P ⟶ F₁.obj X) (q : T ⟶ F₂.obj Z)
    (s : H₁.obj P ⟶ Y) (t : H₂.obj X ⟶ Z)
    (a₁ : G₁.obj P ⟶ U) (a₂ : G₂.obj Y ⟶ J)
    (v : H₂.obj U ⟶ U') (b₂ : N ⟶ F₂.obj J)
    (c : U ⟶ X) (i : Y ⟶ N) (z : J ⟶ U') (c' : U' ⟶ Z)
    (k : N ⟶ T) (n : Y ⟶ T)
    (hc : G₁.map p ≫ ad₁.counit.app X = a₁ ≫ c)
    (hu : ad₂.unit.app Y ≫ F₂.map a₂ = i ≫ b₂)
    (hθ : θ.natTrans.app P ≫ H₂.map a₁ ≫ v = G₂.map s ≫ a₂ ≫ z)
    (h₄ : H₂.map c ≫ t = v ≫ c')
    (h₇ : k ≫ q = b₂ ≫ F₂.map (z ≫ c'))
    (hn : i ≫ k = n) :
    H₁.map p ≫ (mateEquiv ad₁ ad₂ θ).natTrans.app X ≫ F₂.map t =
      s ≫ n ≫ q := by
  have hmate : (mateEquiv ad₁ ad₂ θ).natTrans.app X =
      ad₂.unit.app (H₁.obj (F₁.obj X)) ≫
        F₂.map (θ.natTrans.app (F₁.obj X)) ≫
        F₂.map (H₂.map (ad₁.counit.app X)) := by
    simp [mateEquiv_apply]
  have h₁ := ad₂.unit.naturality (H₁.map p)
  have h₂ := θ.natTrans.naturality p
  have h₅ := ad₂.unit.naturality s
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₅
  rw [hmate]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [reassoc_of% h₂, ← CategoryTheory.Functor.map_comp_assoc H₂, hc,
    CategoryTheory.Functor.map_comp_assoc, h₄, reassoc_of% hθ]
  simp only [CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% h₅, reassoc_of% hu]
  simp only [CategoryTheory.Functor.map_comp] at h₇ ⊢
  rw [← h₇]
  simpa only [Category.assoc] using congrArg (fun f ↦ s ≫ f ≫ q) hn

private theorem scalar_preservesKFlatQuasiIso
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso := by
  exact ProEtale.scalarExtension_preservesKFlat T.smallEtaleTopology φ

section ScalarRepresentativeComparison
variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

private lemma ordinaryScalarRepresentative_isIso
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {L : DerivedCategory D ⥤ DerivedCategory E}
    (b : L ⊣ G.mapDerivedCategory) (P : CochainComplex D ℤ)
    (hP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat P) :
    IsIso ((b.homEquiv _ _).symm
      (DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso D (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) := by
  change IsIso ((ordinaryScalarRepresentative adj DerivedCategory.Q DerivedCategory.Q b
    G.mapDerivedCategoryFactors).app P)
  let c := adj.derivedAdjunction.ofNatIsoRight G.rightDerivedFunctorIsoMapDerivedCategory
  let e := Adjunction.leftAdjointUniq b c
  let ε : F.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have hunit : c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    have h : c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient D (.up ℤ)).obj P)) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient D (.up ℤ)).obj P)) :=
      ProEtale.derived_adjunction_unit_normalization adj
        ((HomotopyCategory.quotient D (.up ℤ)).obj P)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
    change c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient E (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) at h
    have he := G.mapDerivedCategoryFactorsh_hom_app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom] at he
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at he
    have heq : G.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient E (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
        G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
      Iso.ext he
    have hi : G.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient E (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
      congrArg Iso.inv heq
    rw [← hi]
    apply (Iso.eq_comp_inv (G.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient E (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)))).2
    simpa only [Category.assoc, Iso.app_hom] using h
  have hrepr : (ordinaryScalarRepresentative adj DerivedCategory.Q DerivedCategory.Q b
      G.mapDerivedCategoryFactors).app P =
      e.hom.app (DerivedCategory.Q.obj P) ≫ ε := by
    apply (b.homEquiv _ _).injective
    rw [b.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [hunit]
    change (b.homEquiv _ _)
      ((b.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply congrArg (fun t ↦ DerivedCategory.Q.map t ≫
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    ext n
    simp only [Functor.id_obj, Functor.comp_obj, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Adjunction.mapHomologicalComplex_unit_app_f]
    exact Category.comp_id _
  rw [hrepr]
  have : IsIso ε := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  infer_instance

end ScalarRepresentativeComparison

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors DerivedCategory.Qh
  Functor.rightDerivedFunctorUnit Functor.leftDerivedFunctorCounit
  Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

private lemma geometricRepresentative_app
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (leftComparisonTransformation (upperStar (ModuleCat.{u + 1} A) r)
      (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctorCounit).app C =
      scalarGeometricRepresentative A r C := by
  exact Eq.refl (scalarGeometricRepresentative A r C)

private lemma acyclicComparisonTransformation_app
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (acyclicComparisonTransformation (lowerStar (ModuleCat.{u + 1} A) r)).app C =
      properAcyclicComparison A r C := by
  exact Eq.refl (properAcyclicComparison A r C)

private lemma scalarRepresentativeTransformation_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarRepresentativeTransformation φ T).app C =
      scalarExtensionRepresentative φ T C := by
  exact Eq.refl (scalarExtensionRepresentative φ T C)

private lemma acyclicComparison_naturality
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    {C C' : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : C ⟶ C') :
    DerivedCategory.Q.map
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
        properAcyclicComparison A r C' =
      properAcyclicComparison A r C ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) := by
  have hn := (acyclicComparisonTransformation (lowerStar (ModuleCat.{u + 1} A) r)).naturality h
  simpa only [acyclicComparisonTransformation_app, Functor.comp_obj, Functor.comp_map,
    rightDerivedLowerStar] using hn

private lemma scalarRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarExtensionRepresentative φ T P) := by
  have : (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso :=
    scalar_preservesKFlatQuasiIso φ T
  dsimp only [scalarExtensionRepresentative]
  exact ordinaryScalarRepresentative_isIso (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) P hP

private lemma complex_iso_transformation
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (I : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    (Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm).hom =
      complexTransformation F G H I e.hom := by
  ext C n
  simp only [complexTransformation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).symm

private lemma complex_mate
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    {G₁ : C₁ ⥤ C₂} {F₁ : C₂ ⥤ C₁} (adj₁ : G₁ ⊣ F₁)
    {G₂ : C₃ ⥤ C₄} {F₂ : C₄ ⥤ C₃} (adj₂ : G₂ ⊣ F₂)
    (H₁ : C₁ ⥤ C₃) (H₂ : C₂ ⥤ C₄)
    [G₁.Additive] [F₁.Additive] [G₂.Additive] [F₂.Additive]
    [H₁.Additive] [H₂.Additive]
    (σ : TwoSquare H₁ G₁ G₂ H₂) (C : CochainComplex C₂ ℤ) :
    (mateEquiv (adj₁.mapHomologicalComplex (.up ℤ))
      (adj₂.mapHomologicalComplex (.up ℤ))
      (TwoSquare.mk _ _ _ _ (complexTransformation H₁ G₂ G₁ H₂ σ.natTrans))).natTrans.app C =
      (complexTransformation F₁ H₁ H₂ F₂ (mateEquiv adj₁ adj₂ σ).natTrans).app C := by
  ext n
  simp only [complexTransformation, mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.id_f, Category.id_comp, Category.assoc]
  dsimp only [Functor.mapHomologicalComplex]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.comp_id]

private lemma geometric_counit_normalization
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) r).map (properAcyclicComparison A r C) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app
          (DerivedCategory.Q.obj C) =
      scalarGeometricRepresentative A r
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex
            (.up ℤ)).counit.app C) := by
  simpa only [acyclicComparisonTransformation_app, geometricRepresentative_app,
    derivedUpperStarLowerStarAdjunction] using derived_counit_normalization
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r) C

private lemma geometric_unit_normalization
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).unit.app
          (DerivedCategory.Q.obj C) ≫
        R(lowerStar (ModuleCat.{u + 1} A) r).map (scalarGeometricRepresentative A r C) =
      DerivedCategory.Q.map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex
            (.up ℤ)).unit.app C) ≫
        properAcyclicComparison A r
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) := by
  simpa only [acyclicComparisonTransformation_app, geometricRepresentative_app,
    derivedUpperStarLowerStarAdjunction] using derived_unit_normalization
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r) C

private lemma scalar_pullback_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (scalarPullbackIso φ r).hom.app (DerivedCategory.Q.obj C) ≫
        (scalarExtension φ W).map (scalarGeometricRepresentative A r C) ≫
        scalarExtensionRepresentative φ W
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) =
      L(upperStar (ModuleCat.{u + 1} B) r).map
          (scalarExtensionRepresentative φ V C) ≫
        scalarGeometricRepresentative B r
          (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ r).hom.app C) := by
  exact (scalarPullbackIso_existsUnique φ r).choose_spec.1 C hC

end ProofCalculations

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  scalarExtensionRepresentative scalarGeometricRepresentative properAcyclicComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCounit Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.ofIsGrothendieckAbelian ProEtale.etaleSheafExtendScalars
  mateEquiv scalarPullbackIso derivedUpperStarLowerStarAdjunction
  Adjunction.mapHomologicalComplex
  MorphismProperty.kFlat HomologicalComplex.quasiIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A bounded acyclic flat model computes the canonical proper coefficient mate termwise.
The comparisons alpha_A and alpha_B are the canonical derived units on complexes;
the scalar-extension comparisons are the canonical flat-model counits. The displayed
square identifies the B-linear coefficient mate with the localization of pi_C.

Source: Stacks 0GL6, 015E, 0FND, 06YQ and 07A4
(blueprint: lem-sp-acyclic-flat-proper-coefficient-model).

Proof:
1. Additive direct image and scalar extension preserve the finite support bound.
Bounded complexes with flat terms are K-flat by the source bounded-flat theorem;
braided symmetry identifies the two tensor exactness conditions.
2. The homology/single-object comparison turns the positive homology assumptions
into right acyclicity. The bounded-below acyclic-unit theorem and its compatibility
with the unbounded right derived functor make both specified acyclic comparisons
invertible, including their homotopy quotient factors.
3. Ordinary extension followed by exact faithful restriction is tensoring with B.
Thus extension preserves K-flat quasi-isomorphisms. Uniqueness of left adjoints
identifies the specified scalar representative with the left-derived counit,
preceded by an isomorphism; it is invertible on both K-flat models.
4. Apply the unit and counit factorization formulas for the derived adjunctions
and the K-flat normalization of scalarPullbackIso at the direct-image complex.
Expanding the mate and using naturality gives the required square. Mapping the
ordinary mate to complexes agrees degreewise with the mate of the mapped square,
so its chain map is exactly properCoefficientComplexMap.
5. Package the comparison morphisms as natural transformations. Their naturality
and naturality of the coefficient mate give all six specified equations. -/
theorem acyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {W V : Scheme.{u}} (r : W ⟶ V) [IsProper r] [IsNoetherian W] [IsNoetherian V]
    (φ : A →+* B)
    (C : CochainComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : IsAcyclicFlatProperCoefficientModel φ r C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ∧
      IsIso (properAcyclicComparison A r C) ∧
      IsIso (properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      IsIso (scalarExtensionRepresentative φ W C) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ((properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
          (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
            (scalarExtensionRepresentative φ W C) =
        scalarExtensionRepresentative φ V
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
          properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      (∀ (C' : CochainComplex
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hC' : IsAcyclicFlatProperCoefficientModel φ r C') (h : C ⟶ C'),
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              ((properCoefficientTensor φ W).map (DerivedCategory.Q.map h)) =
          (properCoefficientTensor φ V).map
              ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
                (DerivedCategory.Q.map h)) ≫
            (properCoefficientMap φ r).app (DerivedCategory.Q.obj C') ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properAcyclicComparison A r C' =
          properAcyclicComparison A r C ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ≫
            properAcyclicComparison B r (coefficientExtendedComplex φ W C') =
          properAcyclicComparison B r (coefficientExtendedComplex φ W C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              (DerivedCategory.Q.map
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ∧
        (properCoefficientTensor φ W).map (DerivedCategory.Q.map h) ≫
            scalarExtensionRepresentative φ W C' =
          scalarExtensionRepresentative φ W C ≫ DerivedCategory.Q.map
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h) ∧
        (properCoefficientTensor φ V).map (DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ≫
            scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C') =
          scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
            DerivedCategory.Q.map
              (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
                (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ∧
        ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properCoefficientComplexMap φ r C' =
          properCoefficientComplexMap φ r C ≫
            ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) := by
  -- Use the source bounded-flat and acyclic-unit results in this coefficient encoding.
  -- The canonical scalar/pullback normalization supplies the mate comparison.
  have hD : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
      ((((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C).X n) := by
    obtain ⟨a, b, hb⟩ := hC.1
    exact ⟨a, b, fun n hn ↦ Functor.map_isZero (lowerStar (ModuleCat.{u + 1} A) r) (hb n hn)⟩
  have hCW := bounded_flat_sheaf_kFlat A W C hC.1 hC.2.1
  have hDV := bounded_flat_sheaf_kFlat A V _ hD hC.2.2.1
  refine ⟨hCW, hDV, ?_, ?_, scalarRepresentative_isIso φ W C hCW,
    scalarRepresentative_isIso φ V _ hDV, ?_, ?_⟩
  · obtain ⟨a, b, hb⟩ := hC.1
    have : C.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
      (fun n hn ↦ hb n (Or.inl hn))
    exact properAcyclicComparison_isIso A r C a hC.2.2.2.1
  · obtain ⟨a, b, hb⟩ := hC.1
    have : (coefficientExtendedComplex φ W C).IsStrictlyGE a :=
      (CochainComplex.isStrictlyGE_iff _ _).2 (fun n hn ↦
        Functor.map_isZero (ProEtale.etaleSheafExtendScalars φ W) (hb n (Or.inl hn)))
    exact properAcyclicComparison_isIso B r (coefficientExtendedComplex φ W C) a
      hC.2.2.2.2
  · set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    exact (by
      let a : (upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⊣
          (lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) :=
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)
      let b : (upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ) ⊣
          (lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ) :=
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)
      let σ := TwoSquare.mk
        ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ))
        ((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ))
        ((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ))
        ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ))
        (scalarSheafPullbackComplexIso φ r).hom
      let θ := TwoSquare.mk (scalarExtension φ V)
        L(upperStar (ModuleCat.{u + 1} A) r) L(upperStar (ModuleCat.{u + 1} B) r)
        (scalarExtension φ W) (scalarPullbackIso φ r).hom
      let D := ((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C
      have hn : θ.natTrans.app (DerivedCategory.Q.obj D) ≫
          (scalarExtension φ W).map (scalarGeometricRepresentative A r D) ≫
            scalarExtensionRepresentative φ W
              (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D) =
          L(upperStar (ModuleCat.{u + 1} B) r).map
              (scalarExtensionRepresentative φ V D) ≫
            scalarGeometricRepresentative B r
              (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj D) ≫
            DerivedCategory.Q.map (σ.natTrans.app D) := by
        dsimp only [θ, σ, TwoSquare.mk, TwoSquare.natTrans]
        exact scalar_pullback_normalization φ r D hDV
      have hs : (scalarSheafPullbackComplexIso φ r).hom =
          complexTransformation (ProEtale.etaleSheafExtendScalars φ V)
            (upperStar (ModuleCat.{u + 1} B) r) (upperStar (ModuleCat.{u + 1} A) r)
            (ProEtale.etaleSheafExtendScalars φ W) (scalarSheafPullbackIso φ r).hom :=
        by
          dsimp only [scalarSheafPullbackComplexIso]
          exact complex_iso_transformation _ _ _ _ (scalarSheafPullbackIso φ r)
      have hm : (mateEquiv a b σ).natTrans.app C = properCoefficientComplexMap φ r C := by
        dsimp only [σ]
        rw [hs]
        dsimp only [properCoefficientComplexMap, properSheafCoefficientMap]
        simpa only [complexTransformation, NatTrans.comp_app] using
          complex_mate (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
          (ProEtale.etaleSheafExtendScalars φ V) (ProEtale.etaleSheafExtendScalars φ W)
          (TwoSquare.mk (ProEtale.etaleSheafExtendScalars φ V)
            (upperStar (ModuleCat.{u + 1} A) r) (upperStar (ModuleCat.{u + 1} B) r)
            (ProEtale.etaleSheafExtendScalars φ W) (scalarSheafPullbackIso φ r).hom) C
      let E := (ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)
      let M := ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj D
      let τ := σ.natTrans.app D ≫ E.map (a.counit.app C)
      have hc : L(upperStar (ModuleCat.{u + 1} A) r).map
            (properAcyclicComparison A r C) ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app
            (DerivedCategory.Q.obj C) =
          scalarGeometricRepresentative A r D ≫ DerivedCategory.Q.map (a.counit.app C) := by
        exact geometric_counit_normalization A r C
      have hu :
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r).unit.app
              (DerivedCategory.Q.obj M) ≫
            R(lowerStar (ModuleCat.{u + 1} B) r).map
              (scalarGeometricRepresentative B r M) =
          DerivedCategory.Q.map (b.unit.app M) ≫ properAcyclicComparison B r
            (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj M) := by
        exact geometric_unit_normalization B r M
      have h₄ := (scalarRepresentativeTransformation φ W).naturality (a.counit.app C)
      simp only [Functor.comp_map] at h₄
      rw [scalarRepresentativeTransformation_app, scalarRepresentativeTransformation_app] at h₄
      have h₇ := (acyclicComparisonTransformation
        (lowerStar (ModuleCat.{u + 1} B) r)).naturality τ
      simp only [Functor.comp_map] at h₇
      rw [acyclicComparisonTransformation_app, acyclicComparisonTransformation_app] at h₇
      have hτ : DerivedCategory.Q.map τ =
          DerivedCategory.Q.map (σ.natTrans.app D) ≫
            DerivedCategory.Q.map (E.map (a.counit.app C)) := by
        exact CategoryTheory.Functor.map_comp DerivedCategory.Q _ _
      rw [hτ] at h₇
      have hn' : DerivedCategory.Q.map (b.unit.app M) ≫
          DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map τ) =
          DerivedCategory.Q.map (properCoefficientComplexMap φ r C) := by
        rw [← CategoryTheory.Functor.map_comp, ← hm]
        congr 1
        exact (mate_component a b σ C).symm
      exact mate_comparison
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r) θ
        (properAcyclicComparison A r C)
        (properAcyclicComparison B r (coefficientExtendedComplex φ W C))
        (scalarExtensionRepresentative φ V D) (scalarExtensionRepresentative φ W C)
        (scalarGeometricRepresentative A r D) (scalarGeometricRepresentative B r M)
        (scalarExtensionRepresentative φ W
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D))
        (properAcyclicComparison B r
          (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj M))
        (DerivedCategory.Q.map (a.counit.app C)) (DerivedCategory.Q.map (b.unit.app M))
        (DerivedCategory.Q.map (σ.natTrans.app D))
        (DerivedCategory.Q.map (E.map (a.counit.app C)))
        (DerivedCategory.Q.map
          (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map τ))
        (DerivedCategory.Q.map (properCoefficientComplexMap φ r C)) hc hu hn h₄
        (by simpa only [E, M, coefficientExtendedComplex, Functor.comp_obj,
          Functor.id_obj] using h₇) hn')
  · intro C' hC' h
    refine ⟨?_, acyclicComparison_naturality A r h,
      acyclicComparison_naturality B r _, ?_, ?_, ?_⟩
    · simpa only [Functor.comp_obj, Functor.comp_map, properCoefficientTensor,
        rightDerivedLowerStar] using
        ((properCoefficientMap φ r).naturality (DerivedCategory.Q.map h)).symm
    · simpa only [scalarRepresentativeTransformation_app, Functor.comp_obj,
        Functor.comp_map, properCoefficientTensor, complexLocalization] using
        (scalarRepresentativeTransformation φ W).naturality h
    · simpa only [scalarRepresentativeTransformation_app, Functor.comp_obj,
        Functor.comp_map, properCoefficientTensor, complexLocalization] using
        (scalarRepresentativeTransformation φ V).naturality
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)
    · simpa only [coefficientComplexTransformation, complexTransformation,
        properCoefficientComplexMap, coefficientExtendedComplex, NatTrans.comp_app,
        Functor.comp_obj, Functor.comp_map] using
        (coefficientComplexTransformation φ r).naturality h

end AlgebraicGeometry.Etale
