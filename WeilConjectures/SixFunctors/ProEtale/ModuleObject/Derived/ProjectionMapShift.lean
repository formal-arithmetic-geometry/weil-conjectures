/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!
# The projection map of module objects commutes with the shifts

Let `Λ` be a commutative condensed ring and `p : X ⟶ Y` a morphism of schemes. The projection
map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of module objects over `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.projectionMap`) commutes with the shifts in each
variable, as does the tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`) out of which it is built.
This is the compatibility of the projection map with the triangulated structure ("the projection
map is compatible with shifts and cones") used when extending the projection formula from
`Dbc` to `Loc(Dbc)`.

The tensor comparison `m` is handled as in the étale case
(`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift`), through
`DerivedCategory.commShift_of_tensorLeft_fac`: for a K-flat complex `A` whose pullback `p^* A`
is K-flat, the value of `m` at `Qh A` is determined by the counit `Qh ⋙ Lp^* ⟶ p^* ⋙ Qh` of
the derived pullback and by the comparison `p^*(A ⊗ B) ⟶ p^* A ⊗ p^* B` induced by the
comonoidal structure of the strong monoidal functor `p^*`, which is inverse to the comparison
used to define `m` (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_δ`).
Every object is isomorphic to such a `Qh A`, since `p^*` preserves K-flat complexes
(`AlgebraicGeometry.ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`).

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_leftDerivedUpperStarTensor_app`,
  `AlgebraicGeometry.ProEtale.CondensedRing.commShift_leftDerivedUpperStarTensor_flipApp`: the
  tensor comparison commutes with the shifts in each variable.
- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_projectionMap_app`: the projection map
  commutes with the shifts in `L`.
- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_projectionMap_flipApp`: the projection map
  commutes with the shifts in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

set_option hygiene false in
/-- The homotopy category `K(Mod_{Λ_Z})` of module objects over `Λ_Z`. -/
local notation "𝐊(" Z ")" =>
  HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (ComplexShape.up ℤ)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-! ### K-flatness of pullbacks -/

/-- The extension of scalars along the isomorphism `α_p : p^* Λ_Y ⟶ Λ_X` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom :
    (Mod.extendScalars (condensedPullbackHom Λ p)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ p)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ p)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ p)).symm

/-- The pullback of module objects preserves K-flat complexes. -/
lemma kFlat_upperStar_mapHomologicalComplex_obj
    {P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((p)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj P) :=
  ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl ((p)^*⟦Λ⟧)) (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ p)).kFlat_mapHomologicalComplex_obj_of_isEquivalence
      (((p)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).kFlat_mapHomologicalComplex_obj P hP))

/-! ### The tensor comparison on the homotopy category -/

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `p^* A ⊗ p^* B ⟶ p^*(A ⊗ B)` of complexes is a section of the comparison
induced by the comonoidal structure of `p^*`. -/
lemma upperStarTensorComplexHom_δ
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ p A B ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (p)^*⟦Λ⟧).app A).app B =
      𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, 
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  dsimp only [upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Category.comp_id]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The counit of the bifunctor `Lp^* - ⊗ᴸ Lp^* -` on objects of the homotopy category. -/
lemma leftDerivedUpperStarTensorRightCounit_app_app (A B : 𝐊(Y)) :
    ((leftDerivedUpperStarTensorRightCounit Λ p).app A).app B =
      ((p)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((p)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ Qh (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ p A.as B.as)) := by
  dsimp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app]
  erw [Category.id_comp]
  refine (?_ : _ = 𝟙 _ ≫ (((p)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((p)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app B)) ≫
        (Functor.LaxMonoidal.μ Qh (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ p A.as B.as)))).trans ?_
  · rfl
  · exact (Category.id_comp _).trans (Category.assoc _ _ _)


set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The defining property of the tensor comparison of `Lp^*`, in the form used by
`DerivedCategory.commShift_of_tensorLeft_fac`. -/
lemma leftDerivedUpperStarTensor_app_app_fac (A B : 𝐊(Y)) :
    ((leftDerivedUpperStarTensor Λ p).app (Qh.obj A)).app (Qh.obj B) ≫
        (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((p)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((p)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh A B) ≫
        (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (p)^*⟦Λ⟧).app A).app B) := by
  have h : ((leftDerivedUpperStarTensor Λ p).app (Qh.obj A)).app (Qh.obj B) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ p).app A).app B =
      ((leftDerivedUpperStarTensorLeftCounit Λ p).app A).app B :=
    congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ p) A) B
  rw [leftDerivedUpperStarTensorRightCounit_app_app] at h
  have hδ : Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ p A.as B.as)) ≫
      Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (p)^*⟦Λ⟧).app A).app B) = 𝟙 _ := by
    rw [← Functor.map_comp]
    erw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
    rw [← Functor.map_comp, upperStarTensorComplexHom_δ]
    exact (congrArg Qh.map ((HomotopyCategory.quotient _ _).map_id _)).trans (Qh.map_id _)
  calc _ = (((leftDerivedUpperStarTensor Λ p).app (Qh.obj A)).app (Qh.obj B) ≫
        (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((p)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (p)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ p A.as B.as))) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (p)^*⟦Λ⟧).app A).app B) := by
        simp only [Category.assoc]
        erw [hδ, Category.comp_id]
    _ = _ := by
        erw [h]
        exact Category.assoc _ _ _


/-- The pullback of module objects preserves K-flat objects of the homotopy category. -/
lemma kFlat_upperStar_mapHomotopyCategory_obj
    {R : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj R)) :=
  ObjectProperty.prop_of_iso _ (((p)^*⟦Λ⟧.mapHomotopyCategoryFactors (.up ℤ)).app R).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_upperStar_mapHomologicalComplex_obj Λ p hR))

/-- The tensor comparison at `Qh A` commutes with the shifts in the second variable, if `A` and
`p^* A` are K-flat. -/
lemma commShift_leftDerivedUpperStarTensor_app_Qh_obj (A : 𝐊(Y))
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat A)
    (hpA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)) :
    NatTrans.CommShift (F₁ := (curriedTensor _).obj (Qh.obj A) ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor _).obj (L((p)^*⟦Λ⟧).obj (Qh.obj A)))
      ((leftDerivedUpperStarTensor Λ p).app (Qh.obj A)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac (p)^*⟦Λ⟧ L((p)^*⟦Λ⟧)
    (p)^*⟦Λ⟧.leftDerivedFunctorCounit A hA hpA _ (fun M ↦
      leftDerivedUpperStarTensor_app_app_fac Λ p A M)


/-! ### Reduction to K-flat objects -/

/-- The tensor comparison `Lp^*(K ⊗ᴸ -) ⟶ Lp^*K ⊗ᴸ Lp^*(-)` for a fixed `K`. -/
noncomputable abbrev leftDerivedUpperStarTensorApp (K : 𝔻(Y)) :
    (curriedTensor 𝔻(Y)).obj K ⋙ L((p)^*⟦Λ⟧) ⟶
      L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj (L((p)^*⟦Λ⟧).obj K) :=
  (leftDerivedUpperStarTensor Λ p).app K

set_option maxHeartbeats 1000000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The compatibility of the tensor comparison with the shifts in the second variable is
invariant under isomorphisms of the first variable. -/
lemma commShift_leftDerivedUpperStarTensor_app_of_iso {K K' : 𝔻(Y)} (e : K ≅ K')
    [NatTrans.CommShift (leftDerivedUpperStarTensorApp Λ p K') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorApp Λ p K) ℤ := by
  have eq : leftDerivedUpperStarTensorApp Λ p K =
      Functor.whiskerRight ((curriedTensor 𝔻(Y)).map e.hom) L((p)^*⟦Λ⟧) ≫
        leftDerivedUpperStarTensorApp Λ p K' ≫
        Functor.whiskerLeft L((p)^*⟦Λ⟧) ((curriedTensor 𝔻(X)).map (L((p)^*⟦Λ⟧).map e.inv)) := by
    have := (leftDerivedUpperStarTensor Λ p).naturality e.hom
    ext M
    have := congr_app this M
    dsimp [leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight] at this ⊢
    rw [reassoc_of% this, ← MonoidalCategory.comp_whiskerRight, ← Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, MonoidalCategory.id_whiskerRight,
      Category.comp_id]
  have : NatTrans.CommShift ((curriedTensor 𝔻(Y)).map e.hom) ℤ := inferInstance
  have : NatTrans.CommShift ((curriedTensor 𝔻(X)).map (L((p)^*⟦Λ⟧).map e.inv)) ℤ :=
    inferInstance
  rw [eq]
  infer_instance

set_option maxHeartbeats 1000000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The compatibility of the tensor comparison with the shifts in the first variable is
invariant under isomorphisms of the second variable. -/
lemma commShift_leftDerivedUpperStarTensor_flipApp_of_iso {K K' : 𝔻(Y)} (e : K ≅ K')
    [NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).flip.obj K' ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj K'))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K') ℤ] :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).flip.obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj K))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K) ℤ := by
  have eq : Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K =
      Functor.whiskerRight ((curriedTensor 𝔻(Y)).flip.map e.hom) L((p)^*⟦Λ⟧) ≫
        Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K' ≫
        Functor.whiskerLeft L((p)^*⟦Λ⟧)
          ((curriedTensor 𝔻(X)).flip.map (L((p)^*⟦Λ⟧).map e.inv)) := by
    ext M
    have := ((leftDerivedUpperStarTensor Λ p).app M).naturality e.hom
    dsimp [leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight,
      Adjunction.comparisonFlipApp] at this ⊢
    rw [reassoc_of% this, ← MonoidalCategory.whiskerLeft_comp, ← Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id]
  have : NatTrans.CommShift ((curriedTensor 𝔻(Y)).flip.map e.hom) ℤ := inferInstance
  have : NatTrans.CommShift ((curriedTensor 𝔻(X)).flip.map (L((p)^*⟦Λ⟧).map e.inv)) ℤ :=
    inferInstance
  rw [eq]
  infer_instance

/-- The tensor comparison at `Qh A` commutes with the shifts in the first variable, if `A` and
`p^* A` are K-flat. -/
lemma commShift_leftDerivedUpperStarTensor_flipApp_Qh_obj (A : 𝐊(Y))
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat A)
    (hpA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)) :
    NatTrans.CommShift (F₁ := (curriedTensor _).flip.obj (Qh.obj A) ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor _).flip.obj (L((p)^*⟦Λ⟧).obj (Qh.obj A)))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) (Qh.obj A)) ℤ :=
  DerivedCategory.commShift_of_tensorRight_fac (p)^*⟦Λ⟧ L((p)^*⟦Λ⟧)
    (p)^*⟦Λ⟧.leftDerivedFunctorCounit A hA hpA _ (fun M ↦
      leftDerivedUpperStarTensor_app_app_fac Λ p M A)

/-- Every object of `D(Mod_{Λ_Y})` is isomorphic to `Qh` of a K-flat complex whose pullback is
K-flat. -/
lemma exists_iso_Qh_obj_kFlat_upperStar (K : 𝔻(Y)) :
    ∃ (A : 𝐊(Y)) (_ : K ≅ Qh.obj A), (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat A ∧
      (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
        (((p)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) := by
  -- Needed to find the K-flat derivability structure on complexes of module objects.
  have (Z : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj Z) := inferInstance
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨R, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  exact ⟨_, e.symm, hP, kFlat_upperStar_mapHomotopyCategory_obj Λ p
    ((HomotopyCategory.kFlat_quotient_obj_iff _).1 hP)⟩

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `L`. -/
instance commShift_leftDerivedUpperStarTensor_app (K : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj (L((p)^*⟦Λ⟧).obj K))
      ((leftDerivedUpperStarTensor Λ p).app K) ℤ := by
  obtain ⟨A, e, hA, hpA⟩ := exists_iso_Qh_obj_kFlat_upperStar Λ p K
  have : NatTrans.CommShift (leftDerivedUpperStarTensorApp Λ p (Qh.obj A)) ℤ :=
    commShift_leftDerivedUpperStarTensor_app_Qh_obj Λ p A hA hpA
  exact commShift_leftDerivedUpperStarTensor_app_of_iso Λ p e

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `K`. -/
instance commShift_leftDerivedUpperStarTensor_flipApp (K : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).flip.obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj K))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K) ℤ := by
  obtain ⟨A, e, hA, hpA⟩ := exists_iso_Qh_obj_kFlat_upperStar Λ p K
  have := commShift_leftDerivedUpperStarTensor_flipApp_Qh_obj Λ p A hA hpA
  exact commShift_leftDerivedUpperStarTensor_flipApp_of_iso Λ p e

/-- The image of a morphism under the derived tensor product commutes with the shifts in the
second variable. -/
instance commShift_curriedTensor_map {Z : Scheme.{u}} {K K' : 𝔻(Z)} (φ : K ⟶ K') :
    NatTrans.CommShift ((curriedTensor 𝔻(Z)).map φ) ℤ :=
  inferInstance

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` commutes with the shifts in `L`. -/
instance commShift_projectionMap_app (M : 𝔻(X)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).obj (R((p)_*⟦Λ⟧).obj M))
      (F₂ := (L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj M) ⋙ R((p)_*⟦Λ⟧))
      ((projectionMap Λ p).app M) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMap_app (derivedUpperStarLowerStarAdjunction Λ p)
    (leftDerivedUpperStarTensor Λ p) M

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` commutes with the shifts in `M`. -/
instance commShift_projectionMap_flipApp (L : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := R((p)_*⟦Λ⟧) ⋙ (curriedTensor 𝔻(Y)).flip.obj L)
      (F₂ := (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj L) ⋙ R((p)_*⟦Λ⟧))
      (NatTrans.flipApp (projectionMap Λ p) L) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMapFlipApp (derivedUpperStarLowerStarAdjunction Λ p)
    (leftDerivedUpperStarTensor Λ p) ℤ L

end AlgebraicGeometry.ProEtale.CondensedRing
