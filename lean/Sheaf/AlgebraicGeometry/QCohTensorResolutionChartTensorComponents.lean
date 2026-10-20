module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensor

/-!
# Components of the affine chart tensor comparison

Restore the quarantined component formulas without importing the incompatible upstream
chart model. Proved generic single-factor and total-complex component formulas
supply the tensor calculation.
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
-- Expose the definitional conversions used by the original component formulas to
-- the simplifier's implicit transparency mode.
attribute [local implicit_reducible] Scheme.affineOpens ComplexShape.embeddingDownNat
  ComplexShape.Embedding.mk' Functor.mapHomologicalComplex tilde.functor
  CochainComplex.singleFunctors Functor.map₂HomologicalComplex
  TensorResolutionChartModel_localInst1 TensorResolutionSingleTensor_localInst1 affineMonoidal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] TensorResolutionChartModel_localInst1
  TensorResolutionChartModel_localInst2 TensorResolutionChartModel_localInst3
  TensorResolutionChartModel_localInst4

noncomputable local instance TensorResolutionChartTensorComponents_localInst1 (X :
    Scheme.{u}) : MonoidalCategory X.Modules :=
  TensorResolutionChartModel_localInst1 X
noncomputable local instance TensorResolutionChartTensorComponents_localInst2 (X :
    Scheme.{u}) : MonoidalPreadditive X.Modules :=
  TensorResolutionChartModel_localInst2 X
local instance TensorResolutionChartTensorComponents_localInst3 (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  TensorResolutionChartModel_localInst3 X
local instance TensorResolutionChartTensorComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  TensorResolutionChartModel_localInst4 X M


section
variable {C₁ : Type u} {C₂ : Type v} {D : Type w}
  [Category C₁] [Category C₂] [Category D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]

/-- The inverse single-factor comparison includes the degree-(i,0) summand. -/
private theorem single₂_inv_f (E : CochainComplex C₁ ℤ) (N : C₂) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso F N E).inv.f i =
      (F.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫
        HomologicalComplex.ιMapBifunctor E
          ((HomologicalComplex.single C₂ (.up ℤ) 0).obj N) F (.up ℤ) i 0 i (by simp) := by
  dsimp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv,
    HomologicalComplex.comp_f, Iso.symm_inv]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp [ComplexShape.σ]

variable [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
  HomologicalComplex.HasMapBifunctor K₁ K₂ F (.up ℤ)]

/-- Single-factor comparison followed by a map in the second variable.

Naturality of the degree-(i,0) inclusion and functoriality combine the two
maps of the second coefficient before its inclusion in the total complex. -/
private theorem single₂_inv_map_f (E : CochainComplex C₁ ℤ)
    (B : CochainComplex C₂ ℤ) (N : C₂)
    (e : (HomologicalComplex.single C₂ (.up ℤ) 0).obj N ⟶ B) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso F N E).inv.f i ≫
        ((F.map₂CochainComplex.obj E).map e).f i =
      (F.obj (E.X i)).map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫ e.f 0) ≫
        HomologicalComplex.ιMapBifunctor E B F (.up ℤ) i 0 i (by simp) := by
  dsimp only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  rw [single₂_inv_f]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_comp]
end

section
variable {C : Type u} [Category C] [MonoidalCategory C] [Preadditive C]
  [HasZeroObject C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ X, ((curriedTensor C).obj X).PreservesZeroMorphisms]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (.up ℤ)]

/-- Combining the two single-factor tensor components with arbitrary leading maps. -/
private theorem tensor_single_tail (E B : CochainComplex C ℤ) (N : C) (i : ℤ)
    {Z X : C} (a : Z ⟶ X ⊗ N) (b : X ⟶ E.X i)
    (e : (HomologicalComplex.single C (.up ℤ) 0).obj N ⟶ B)
    (g : N ⟶ B.X 0)
    (hg : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫ e.f 0 = g) :
    a ≫ (tensorRight N).map b ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) N E).inv.f i ≫
        (((curriedTensor C).map₂CochainComplex.obj E).map e).f i =
      a ≫ (b ⊗ₘ g) ≫
        HomologicalComplex.ιMapBifunctor E B (curriedTensor C) (.up ℤ) i 0 i (by simp) := by
  rw [single₂_inv_map_f (curriedTensor C) E B N e i, hg]
  simp only [curriedTensor_obj_map, tensorHom_def, Category.assoc]
  rfl
end

/-- The natural tensor comparison has its prescribed affine component. -/
private theorem tildeTensorRightIso_hom_app (A : Type u) [CommRing A]
    (N M : ModuleCat.{u} A) :
    (tensorResolutionTildeTensorRightIso A N).hom.app M =
      tensorResolutionTildeTensorHom A M N := rfl

/-- The degree-zero single comparison after a model isomorphism. -/
private theorem single_model_map_f
    {C : Type u} {D : Type v} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (N : C) (NA : D) (s : NA ≅ F.obj N) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 NA).inv ≫
        ((CochainComplex.singleFunctor D 0).map s.hom ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app N).inv).f 0 =
      s.hom ≫ F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv := by
  simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc]

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

section
variable {C : Type u} {D : Type v} [Category C] [Category D]
  [HasZeroMorphisms C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalCategory D]
  [(curriedTensor D).PreservesZeroMorphisms]
  [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
  [∀ (K₁ K₂ : CochainComplex D ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor D) (.up ℤ)]

/-- Naturality moves the extension comparison through a tensor comparison before
including the single-factor summand. Keeping the categories abstract avoids
normalizing the sheaf tensor structure at every step of this calculation. -/
private theorem map_extend_tensor_component (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (G : C ⥤ C) [G.PreservesZeroMorphisms] (N : D)
    (s : G ⋙ F ⟶ F ⋙ tensorRight N)
    (K : ChainComplex C ℕ) (B : CochainComplex D ℤ)
    (e : (HomologicalComplex.single D (.up ℤ) 0).obj N ⟶ B)
    (g : N ⟶ B.X 0)
    (hg : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫ e.f 0 = g)
    (j : ℕ) :
    let i := -(j : ℤ)
    let L := (G.mapHomologicalComplex (.down ℕ)).obj K
    let E := (F.mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)
    F.map (L.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv ≫
        F.map ((tensorResolutionMapExtendIso G
          ComplexShape.embeddingDownNat K).inv.f i) ≫
        s.app ((K.extend ComplexShape.embeddingDownNat).X i) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) N E).inv.f i ≫
        (((curriedTensor D).map₂CochainComplex.obj E).map e).f i =
      s.app (K.X j) ≫
        (F.map (K.extendXIso ComplexShape.embeddingDownNat
          (i := j) (i' := i) rfl).inv ⊗ₘ g) ≫
        HomologicalComplex.ιMapBifunctor E B (curriedTensor D) (.up ℤ) i 0 i (by simp) := by
  dsimp only
  rw [← Functor.map_comp_assoc]
  rw [tensorResolutionMapExtendIso_inv_f G
    ComplexShape.embeddingDownNat K (i := j) (i' := -(j : ℤ)) rfl]
  simp only [Iso.inv_hom_id_assoc]
  have hs := s.naturality
    (K.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := -(j : ℤ)) rfl).inv
  change F.map (G.map _) ≫ _ = _
  rw [reassoc_of% hs]
  exact tensor_single_tail
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat))
    B N (-(j : ℤ)) (s.app (K.X j))
    (F.map (K.extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := -(j : ℤ)) rfl).inv) e g hg
end

/-- Affine form of the abstract calculation, normalized at the bundled ring. -/
private theorem tilde_map_extend_tensor_component (A : CommRingCat.{u})
    (NA : ModuleCat.{u} A) (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (B : CochainComplex (Spec A).Modules ℤ)
    (e : (HomologicalComplex.single (Spec A).Modules (.up ℤ) 0).obj
      (tilde (R := A) NA) ⟶ B)
    (g : tilde (R := A) NA ⟶ B.X 0)
    (hg : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde (R := A) NA)).inv ≫
      e.f 0 = g) (j : ℕ) :
    let _ : (tilde.functor A).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    let i := -(j : ℤ)
    let L := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj K
    let E := ((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)
    tilde.map (L.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv ≫
        tilde.map ((tensorResolutionMapExtendIso (tensorRight NA)
          ComplexShape.embeddingDownNat K).inv.f i) ≫
        tensorResolutionTildeTensorHom (A : Type u)
          ((K.extend ComplexShape.embeddingDownNat).X i) NA ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Spec A).Modules)
          (tilde (R := A) NA) E).inv.f i ≫
        (((curriedTensor (Spec A).Modules).map₂CochainComplex.obj E).map e).f i =
      tensorResolutionTildeTensorHom (A : Type u) (K.X j) NA ≫
        (tilde.map (K.extendXIso ComplexShape.embeddingDownNat
          (i := j) (i' := i) rfl).inv ⊗ₘ g) ≫
        HomologicalComplex.ιMapBifunctor E B (curriedTensor (Spec A).Modules)
          (.up ℤ) i 0 i (by simp) := by
  cases A
  rename_i A instA
  let : (tilde.functor (.of A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  simpa only [tilde.functor_map, tildeTensorRightIso_hom_app] using
    map_extend_tensor_component (C := ModuleCat.{u} A) (D := (Spec (.of A)).Modules)
      (tilde.functor (.of A)) (tensorRight NA) (tilde (R := .of A) NA)
      (tensorResolutionTildeTensorRightIso A NA).hom K B e g hg j

set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] TensorResolutionChartTensorComponents_localInst1
attribute [local irreducible] SheafOfModules.monoidalCategory

set_option maxHeartbeats 800000 in
-- Keep the tensor-resolution component calculation within its existing heartbeat budget.
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
  set_option backward.isDefEq.respectTransparency.types true in
    dsimp only
    let eN := (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
      (tensorResolutionChartModel N U NA sN).hom ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app N).inv
    dsimp only [tensorResolutionChartTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      HomologicalComplex.comp_f, Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, tildeTensorRightIso_hom_app]
    exact tilde_map_extend_tensor_component Γ(Y, U.1) NA P.complex
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N)) eN
      ((tensorResolutionChartModel N U NA sN).hom ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)
      (single_model_map_f (Scheme.Modules.restrictFunctor U.2.fromSpec) N
        (tilde (R := Γ(Y, U.1)) NA) (tensorResolutionChartModel N U NA sN)) j

end AlgebraicGeometry
