module

public import Sheaf.Paper.CompactSupportScalarLimitReduction
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Coherence of the normalized tensor and arithmetic limit comparisons

Source: Stacks Tag 0941; auxiliary Step 7 of strict compact-support scalar composition.
(blueprint: lem-pur-scalar-limit-tensor-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.PurStrictScalar.scalarLimitTensor
  WeilConjectures.PurStrictScalar.scalarLimitRestriction
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace ScalarRestrictionProof

private theorem ordinary_square
    {A B : Type*} [Category A] [Category B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (U : A ⥤ B) [PreservesLimitsOfShape ℕᵒᵖ U]
    (P : ℕᵒᵖ ⥤ ℕᵒᵖ) (M : ℕᵒᵖ ⥤ A) :
    U.map (limit.pre M P) ≫ (preservesLimitNatIso (J := ℕᵒᵖ) U).hom.app (P ⋙ M) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).map (𝟙 ((P ⋙ M) ⋙ U)) =
      (preservesLimitNatIso (J := ℕᵒᵖ) U).hom.app M ≫ limit.pre (M ⋙ U) P := by
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply limit.hom_ext
  intro n
  change (U.map (limit.pre M P) ≫ (preservesLimitIso U (P ⋙ M)).hom) ≫
      limit.π (P ⋙ (M ⋙ U)) n =
    ((preservesLimitIso U M).hom ≫ limit.pre (M ⋙ U) P) ≫ limit.π _ n
  erw [Category.assoc, preservesLimitIso_hom_π U (P ⋙ M) n,
    ← U.map_comp, limit.pre_π M P n, Category.assoc, limit.pre_π (M ⋙ U) P n,
    preservesLimitIso_hom_π U M (P.obj n)]

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (H : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (U : B ⥤ D)
  [H.Additive] [G.Additive] [V.Additive] [U.Additive]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [V.PreservesKInjectiveComplexes]

private def comparison (c : H ⋙ U ≅ V ⋙ G) :
    H.rightDerivedFunctor ⋙ U.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H U).symm ≪≫
    Functor.rightDerivedFunctorNatIso c ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso V G

private theorem comparison_fac (c : H ⋙ U ≅ V ⋙ G)
    (I : HomotopyCategory A (.up ℤ)) :
    U.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app I) ≫
        (comparison H G V U c).hom.app (DerivedCategory.Qh.obj I) =
      U.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnit.app ((V.mapHomotopyCategory (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactorsh.inv.app I) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  apply (cancel_epi (U.mapDerivedCategoryFactorsh.inv.app _)).mp
  have hU := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac H U
    ((HomotopyCategory.quotient _ _).obj K)
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at hU
  rw [← Category.assoc, ← hU]
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  erw [Functor.rightDerivedNatTrans_app_assoc]
  simp only [Functor.whiskerRight_app]
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app]
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (V ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  erw [hi, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem pullback_fac (P : A ⥤ A) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (r : H ⟶ P ⋙ H) (I : HomotopyCategory A (.up ℤ)) :
    H.rightDerivedFunctorUnit.app I ≫
        (Functor.rightDerivedPullback P r).app (DerivedCategory.Qh.obj I) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory r (.up ℤ)).app I) ≫
        H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj I) ≫
        H.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.inv.app I) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  exact Functor.rightDerivedPullback_fac_app P r K

private theorem comparison_pullback
    (P : A ⥤ A) (S : C ⥤ C) [P.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (c : H ⋙ U ≅ V ⋙ G) (a : P ⋙ V ≅ V ⋙ S)
    (r : H ⟶ P ⋙ H) (s : G ⟶ S ⋙ G)
    (hc : ∀ M : A,
      U.map (r.app M) ≫ c.hom.app (P.obj M) ≫ G.map (a.hom.app M) =
        c.hom.app M ≫ s.app (V.obj M)) :
    Functor.whiskerRight (Functor.rightDerivedPullback P r) U.mapDerivedCategory ≫
        Functor.whiskerLeft P.mapDerivedCategory (comparison H G V U c).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso a).hom
          G.rightDerivedFunctor =
      (comparison H G V U c).hom ≫
        Functor.whiskerLeft V.mapDerivedCategory (Functor.rightDerivedPullback S s) := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let qK := (HomotopyCategory.quotient A (.up ℤ)).obj K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change U.mapDerivedCategory.map
      ((Functor.rightDerivedPullback P r).app (DerivedCategory.Qh.obj qK)) ≫
      (comparison H G V U c).hom.app
        (P.mapDerivedCategory.obj (DerivedCategory.Qh.obj qK)) ≫
      G.rightDerivedFunctor.map
        ((Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Qh.obj qK)) =
    (comparison H G V U c).hom.app (DerivedCategory.Qh.obj qK) ≫
      (Functor.rightDerivedPullback S s).app
        (V.mapDerivedCategory.obj (DerivedCategory.Qh.obj qK))
  apply (cancel_epi (U.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app qK))).mp
  have hn := (comparison H G V U c).hom.naturality
    (P.mapDerivedCategoryFactorsh.inv.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  have hs := (Functor.rightDerivedPullback S s).naturality
    (V.mapDerivedCategoryFactorsh.inv.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hs
  have ha :
      V.mapDerivedCategoryFactorsh.inv.app ((P.mapHomotopyCategory (.up ℤ)).obj qK) ≫
        V.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.inv.app qK) ≫
        (Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Qh.obj qK) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app qK) ≫
        S.mapDerivedCategoryFactorsh.inv.app ((V.mapHomotopyCategory (.up ℤ)).obj qK) ≫
        S.mapDerivedCategory.map (V.mapDerivedCategoryFactorsh.inv.app qK) := by
    apply (cancel_mono (S.mapDerivedCategory.map (V.mapDerivedCategoryFactorsh.hom.app qK) ≫
      S.mapDerivedCategoryFactorsh.hom.app ((V.mapHomotopyCategory (.up ℤ)).obj qK))).mp
    simp only [Category.assoc]
    rw [Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj]
    simp only [← S.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (V ⋙ S)) (.up ℤ)).inv.app
        qK = 𝟙 _ := by
      change (HomotopyCategory.quotient C (.up ℤ)).map (𝟙 _) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
    rw [hi, Category.id_comp, Category.comp_id]
    erw [S.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
  rw [← U.mapDerivedCategory.map_comp_assoc, pullback_fac H P r qK]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [reassoc_of% (comparison_fac H G V U c
    ((P.mapHomotopyCategory (.up ℤ)).obj qK))]
  erw [← G.rightDerivedFunctor.map_comp, ← G.rightDerivedFunctor.map_comp, ha]
  erw [G.rightDerivedFunctor.map_comp, G.rightDerivedFunctor.map_comp]
  have hu := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hu
  erw [← reassoc_of% hu]
  have hf := U.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory r (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hf
  erw [reassoc_of% hf]
  erw [reassoc_of% (comparison_fac H G V U c qK), hs]
  rw [reassoc_of% (pullback_fac G S s ((V.mapHomotopyCategory (.up ℤ)).obj qK))]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  have hh :
      (U.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory r (.up ℤ)).app qK) ≫
        (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app
          ((P.mapHomotopyCategory (.up ℤ)).obj qK) ≫
        (G.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app qK) =
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app qK ≫
        (NatTrans.mapHomotopyCategory s (.up ℤ)).app
          ((V.mapHomotopyCategory (.up ℤ)).obj qK) := by
    have hk :
        (U.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex r (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (G.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K) =
        (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K ≫
          (NatTrans.mapHomologicalComplex s (.up ℤ)).app
            ((V.mapHomologicalComplex (.up ℤ)).obj K) := by
      ext n
      exact hc (K.X n)
    change (HomotopyCategory.quotient D (.up ℤ)).map
        ((U.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex r (.up ℤ)).app K)) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((G.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex s (.up ℤ)).app
            ((V.mapHomologicalComplex (.up ℤ)).obj K))
    simpa only [Functor.map_comp] using
      (HomotopyCategory.quotient D (.up ℤ)).congr_map hk
  rw [hh]
  rfl

end
end ScalarRestrictionProof

namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Finite-free tensor/limit comparison commutes with the specified arithmetic cone map.
Source: Stacks Tag 0941; compact-support Roos cofinality and finite-free comparison,
auxiliary Step 7 of compact-support strict scalar composition.
(blueprint: lem-pur-scalar-limit-tensor-restriction).
Proof: use a simultaneous strict K-injective resolution. The ordinary arithmetic
cone map selects the coordinates e(n+1)-1; its normalized Roos map has selection
in one coordinate and weighted block sums in the other. Tensor/product comparison
commutes with selection and with each finite weighted sum, since tensor is additive
and uses the same transition maps. Thus the two cochain maps are equal on both
Roos coordinates. The scalarRoosNormalization and scalarRoosTensorNormalization
identities identify these with the displayed canonical maps. Localizing and
cancelling those identifications proves the equation for every derived tower. -/
theorem scalarLimitTensor_restriction (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (baseTensor l E F i W).map ((scalarLimitRestriction l E W e).app K) ≫
        (scalarLimitTensor l E F i W).hom.app ((subsequence l E W e).obj K) ≫
        (scalarLimit l F W).map
          ((letI := (tensor_exact l E F i W).1
            letI := (tensor_exact l E F i W).2
            Functor.mapDerivedCategorySquareIso
              (show ordinarySubsequence l E W e ⋙ tensor l E F i W ≅
                tensor l E F i W ⋙ ordinarySubsequence l F W e from Iso.refl _)).hom.app K) =
      (scalarLimitTensor l E F i W).hom.app K ≫
        (scalarLimitRestriction l F W e).app ((T l E F i W).obj K) := by
  have _he := he
  have := (scalarLimitTensor_exact l E F i W).1
  have := (scalarLimitTensor_exact l E F i W).2.1
  have := (scalarLimitTensor_exact l E F i W).2.2.1
  have := (scalarLimitTensor_exact l E F i W).2.2.2
  let H : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W := lim
  let G : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W := lim
  let V := tensor l E F i W
  let U := pbcExtend (constantMap l E F i W)
  have hc (M : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
      U.map ((scalarLimitRestrictionOrdinary l E W e).app M) ≫
        (preservesLimitNatIso (J := ℕᵒᵖ) U).hom.app
          ((ordinarySubsequence l E W e).obj M) ≫
        G.map ((show ordinarySubsequence l E W e ⋙ V ≅
          V ⋙ ordinarySubsequence l F W e from Iso.refl _).hom.app M) =
      (preservesLimitNatIso (J := ℕᵒᵖ) U).hom.app M ≫
        (scalarLimitRestrictionOrdinary l F W e).app (V.obj M) := by
    exact ScalarRestrictionProof.ordinary_square U
      (CategoryTheory.StrictTowerArithmetic.index e) M
  have h := ScalarRestrictionProof.comparison_pullback H G V U
    (ordinarySubsequence l E W e) (ordinarySubsequence l F W e)
    (preservesLimitNatIso (J := ℕᵒᵖ) U) (Iso.refl _)
    (scalarLimitRestrictionOrdinary l E W e)
    (scalarLimitRestrictionOrdinary l F W e) hc
  simpa only [ScalarRestrictionProof.comparison, scalarLimitTensor, scalarLimitRestriction,
    baseTensor, T, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    using congr_app h K

end WeilConjectures.PurStrictScalar
