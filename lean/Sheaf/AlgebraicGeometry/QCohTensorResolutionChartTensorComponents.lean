module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionChartTensorComponents_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionChartTensorComponents_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionChartTensorComponents_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionChartTensorComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Components of the inverse mapping/extension comparison. -/
theorem tensorResolutionMapExtendIso_inv_f
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (tensorResolutionMapExtendIso F e K).inv.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv := by
  let α := tensorResolutionMapExtendIso F e K
  have he : α.hom.f i' ≫ α.inv.f i' = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f ↦ f.f i') α.hom_inv_id
  apply (cancel_epi (α.hom.f i')).1
  rw [he, ← Category.assoc, tensorResolutionMapExtendIso_f,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

/-- The chart tensor comparison on an original degree of the projective resolution.

After moving the extension isomorphism through the tilde/tensor comparison, use
the flip isomorphism and the `ιMapBifunctor` naturality square.  The degree-zero
component of the single-object comparison is the chart model followed by the
inverse single-object identification; the tensor sign is one because the second
degree is zero.  The final two morphisms coincide because
`(F.mapHomologicalComplex c).obj K |>.X i` is `F.obj (K.X i)` and
`CochainComplex.singleFunctor C 0` is `HomologicalComplex.single C (.up ℤ) 0`.
-/
theorem tensorResolutionChartTensorIso_f {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1)) (P : ProjectiveResolution MA)
    (j : ℕ) :
    let i := -(j : ℤ)
    let L := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex
    let E := tensorResolutionChartComplex U MA P
    let B := ((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)
    tilde.map (L.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv ≫
        (tensorResolutionChartTensorIso N U MA NA sN P).hom.f i =
      tensorResolutionTildeTensorHom _ (P.complex.X j) NA ≫
        (tilde.map (P.complex.extendXIso ComplexShape.embeddingDownNat
            (i := j) (i' := i) rfl).inv ⊗ₘ
          ((tensorResolutionChartModel N U NA sN).hom ≫
            (Scheme.Modules.restrictFunctor U.2.fromSpec).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)) ≫
        HomologicalComplex.ιMapBifunctor E B (curriedTensor _) (.up ℤ) i 0 i (by simp) := by
  sorry
/-
  dsimp only
  dsimp only [tensorResolutionChartTensorIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.comp_f, Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  change tilde.map _ ≫ tilde.map
      ((tensorResolutionMapExtendIso (tensorRight NA)
        ComplexShape.embeddingDownNat P.complex).inv.f (-(j : ℤ))) ≫
      tensorResolutionTildeTensorHom _
        ((P.complex.extend ComplexShape.embeddingDownNat).X (-(j : ℤ))) NA ≫ _ = _
  change (tilde.functor (CommRingCat.of (Γ(Y, U.1)))).map _ ≫
      (tilde.functor (CommRingCat.of (Γ(Y, U.1)))).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc]
  rw [tensorResolutionMapExtendIso_inv_f (tensorRight NA)
    ComplexShape.embeddingDownNat P.complex (i := j) (i' := -(j : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := (tensorResolutionTildeTensorRightIso (Γ(Y, U.1) : Type u) NA).hom.naturality
    (P.complex.extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := -(j : ℤ)) rfl).inv
  change tilde.map _ ≫ tensorResolutionTildeTensorHom _ _ _ =
    tensorResolutionTildeTensorHom _ _ _ ≫ _ at ht
  change tilde.map ((tensorRight NA).map _) ≫ _ = _
  rw [reassoc_of% ht]
  let E := (tensorResolutionChartComplex U MA P)
  let eN := ((CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
    (tensorResolutionChartModel N U NA sN).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app N).inv)
  dsimp only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  simp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.comp_f]
  have hflip := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
    (𝟙 E) eN (curriedTensor (Spec Γ(Y, U.1)).Modules) (.up ℤ)
  have hflipf := congrArg (fun h ↦ h.f (-(j : ℤ))) hflip
  have hflipf' := by simpa only [HomologicalComplex.comp_f] using hflipf
  dsimp [E] at hflipf'
  dsimp [tensorResolutionChartComplex]
  simp only [Category.assoc]
  erw [← hflipf']
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  simp only [Category.assoc]
  have hi := HomologicalComplex.ι_mapBifunctorMap eN (𝟙 E)
    (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ) 0 (-(j : ℤ))
      (-(j : ℤ)) (by simp)
  dsimp [E] at hi
  congr 1
  unfold tensorResolutionChartComplex at hi
  unfold tensorResolutionChartComplex
  change
      ((HomologicalComplex.single (Spec Γ(Y, U.1)).Modules (.up ℤ) 0).obj
          (tilde NA)).ιMapBifunctor
          (((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
            (P.complex.extend ComplexShape.embeddingDownNat))
          (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ) 0 (-(j : ℤ))
            (-(j : ℤ)) (by simp) ≫
        (HomologicalComplex.mapBifunctorMap eN
          (𝟙 (((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
            (P.complex.extend ComplexShape.embeddingDownNat)))
          (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ)).f (-(j : ℤ)) = _ at hi
  rw [reassoc_of% hi]
  change ((curriedTensor (Spec Γ(Y, U.1)).Modules).map _).app _ ≫ _ = _
  simp only [curriedTensor_map_app, Functor.flip_map_app, curriedTensor_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  have heN :
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde NA)).inv ≫ eN.f 0 =
        (tensorResolutionChartModel N U NA sN).hom ≫
          (Scheme.Modules.restrictFunctor U.2.fromSpec).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv := by
    dsimp [eN]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.map_comp, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc]
  rw [tensorHom_def]
  simp only [← curriedTensor_map_app, ← curriedTensor_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    one_smul, Category.assoc]
  have hmap := ((curriedTensor (Spec Γ(Y, U.1)).Modules).obj
      ((((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
        (P.complex.extend ComplexShape.embeddingDownNat)).X (-(j : ℤ)))).map_comp
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde NA)).inv) (eN.f 0)
  rw [← reassoc_of% hmap, heN]
  have hs : (ComplexShape.up ℤ).σ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (-(j : ℤ)) 0 = 1 := by simp [ComplexShape.σ]
  rw [hs, one_smul]
  change _ ≫ _ ≫ (𝟙 _ ≫ _) = _
  rw [Category.id_comp]
  have hfirst :
      ((curriedTensor (Spec Γ(Y, U.1)).Modules).map
        ((tilde.functor (CommRingCat.of (Γ(Y, U.1) : Type u))).map
          (P.complex.extendXIso ComplexShape.embeddingDownNat
            (i := j) (i' := -(j : ℤ)) rfl).inv)).app (tilde NA) =
      ((curriedTensor (Spec Γ(Y, U.1)).Modules).map
        (tilde.map (P.complex.extendXIso ComplexShape.embeddingDownNat
          (i := j) (i' := -(j : ℤ)) rfl).inv)).app (tilde NA) := rfl
  rw [hfirst]
-/

end AlgebraicGeometry
