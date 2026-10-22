/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteFieldDerivedTensorComparison
import Sheaf.Paper.SeparableFieldTensorSheaf
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The separability retraction on total sheaf tensors

Source: Stacks Project, Tags 0C2X, 03EK, 0GMW, 06YN and 06YU.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

private theorem restrictScalars_preservesSmallColimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (α : R ⟶ S) : PreservesColimitsOfSize.{0, 0} (SheafOfModules.restrictScalars.{w} α) := by
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} R) :=
    ⟨fun {I} _ ↦ SheafOfModules.preservesColimitsOfShape_toSheaf R I⟩
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} S) :=
    ⟨fun {I} _ ↦ SheafOfModules.preservesColimitsOfShape_toSheaf S I⟩
  have : ReflectsColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.restrictScalars.{w} α ⋙ SheafOfModules.toSheaf.{w} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} S))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{w} R)

/-- Cache the standard coproduct-based totalization instance before specializing its data. -/
private theorem cochain_hasMapBifunctor
    {A B D : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X : A, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    HomologicalComplex.HasMapBifunctor K L F (.up ℤ) := by
  infer_instance

attribute [local instance] cochain_hasMapBifunctor

namespace TensorTotalization
variable {A B D : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
  {F G H : A ⥤ B ⥤ D}
  [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
  [H.PreservesZeroMorphisms] [∀ X, (H.obj X).PreservesZeroMorphisms]
private noncomputable def map (τ : F ⟶ G) (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    HomologicalComplex.mapBifunctor K L F (.up ℤ) ⟶
      HomologicalComplex.mapBifunctor K L G (.up ℤ) :=
  HomologicalComplex.mapBifunctorComparison
    (G := 𝟭 D) (G₁ := 𝟭 A) (G₂ := 𝟭 B) τ (.up ℤ) K L

@[reassoc] private theorem ι_map (τ : F ⟶ G) (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L F (.up ℤ) i j n h ≫ (map τ K L).f n =
      (τ.app (K.X i)).app (L.X j) ≫
        HomologicalComplex.ιMapBifunctor K L G (.up ℤ) i j n h := by
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (G := 𝟭 D) (G₁ := 𝟭 A) (G₂ := 𝟭 B) τ (.up ℤ) K L i j n h

private theorem map_id (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    map (𝟙 F) K L = 𝟙 _ := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [ι_map, NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f,
    Category.comp_id]

private theorem map_comp (τ : F ⟶ G) (σ : G ⟶ H) (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) : map (τ ≫ σ) K L = map τ K L ≫ map σ K L := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, ι_map, ι_map_assoc, NatTrans.comp_app,
    Category.assoc]

private theorem map_add (τ σ : F ⟶ G) (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    map (τ + σ) K L = map τ K L + map σ K L := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.add_f_apply, ι_map, NatTrans.app_add,
    Preadditive.comp_add, Preadditive.add_comp]

private theorem map_zero (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    map (0 : F ⟶ G) K L = 0 := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.zero_f, ι_map, NatTrans.app_zero,
    Limits.zero_comp, Limits.comp_zero]

private theorem functor_map (F : A ⥤ B ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    {KL KL' : CochainComplex A ℤ × CochainComplex B ℤ} (f : KL ⟶ KL') :
    (Functor.uncurry.obj (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map f =
      HomologicalComplex.mapBifunctorMap f.1 f.2 F (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change HomologicalComplex.ιMapBifunctor KL.1 KL.2 F (.up ℤ) i j n h ≫
    ((HomologicalComplex.mapBifunctorMap f.1 (𝟙 KL.2) F (.up ℤ)).f n ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 KL'.1) f.2 F (.up ℤ)).f n) = _
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  erw [(F.obj (KL'.1.X i)).map_id, F.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private noncomputable def natTrans (τ : F ⟶ G) :
    Functor.uncurry.obj (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⟶
      Functor.uncurry.obj (G.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) where
  app KL := map τ KL.1 KL.2
  naturality KL KL' f := by
    rw [functor_map, functor_map]
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.ι_mapBifunctorMap_assoc, ι_map_assoc, ι_map,
      HomologicalComplex.ι_mapBifunctorMap]
    rw [(τ.app (KL'.1.X i)).naturality_assoc]
    rw [← Category.assoc, ← NatTrans.comp_app, τ.naturality, NatTrans.comp_app]
    simp only [Category.assoc]

@[simp] private theorem natTrans_id : natTrans (𝟙 F) = 𝟙 _ := by
  apply NatTrans.ext
  funext KL
  exact map_id KL.1 KL.2

@[simp] private theorem natTrans_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    natTrans (τ ≫ σ) = natTrans τ ≫ natTrans σ := by
  apply NatTrans.ext
  funext KL
  exact map_comp τ σ KL.1 KL.2

@[simp] private theorem natTrans_add (τ σ : F ⟶ G) :
    natTrans (τ + σ) = natTrans τ + natTrans σ := by
  apply NatTrans.ext
  funext KL
  exact map_add τ σ KL.1 KL.2

@[simp] private theorem natTrans_zero : natTrans (0 : F ⟶ G) = 0 := by
  apply NatTrans.ext
  funext KL
  exact map_zero KL.1 KL.2

private noncomputable def ringHom : End F →+* End
    (Functor.uncurry.obj (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))) where
  toFun := natTrans
  map_zero' := natTrans_zero
  map_one' := natTrans_id
  map_add' := natTrans_add
  map_mul' a b := natTrans_comp b a

private noncomputable def evaluationRingHom {A D : Type*} [Category A] [Category D]
    [Preadditive D] (T : A ⥤ D) (X : A) : End T →+* End (T.obj X) where
  toFun f := f.app X
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem evaluationRingHom_apply {A D : Type*} [Category A] [Category D]
    [Preadditive D] (T : A ⥤ D) (X : A) (f : End T) :
    evaluationRingHom T X f = f.app X := rfl

private noncomputable def conjugateEndRing {D : Type*} [Category D] [Preadditive D]
    {X Y : D} (i : X ≅ Y) : End X →+* End Y where
  toFun f := i.inv ≫ f ≫ i.hom
  map_zero' := by simp
  map_one' := by simp only [End.one_def, Category.id_comp, Iso.inv_hom_id]
  map_add' _ _ := by
    change i.inv ≫ (_ + _) ≫ i.hom = _
    simp only [Preadditive.comp_add, Preadditive.add_comp]
  map_mul' _ _ := by simp only [End.mul_def, Category.assoc, Iso.hom_inv_id_assoc]

private theorem conjugateEndRing_apply {D : Type*} [Category D] [Preadditive D]
    {X Y : D} (i : X ≅ Y) (f : End X) :
    conjugateEndRing i f = i.inv ≫ f ≫ i.hom := rfl

private theorem transport_split {D : Type*} [Category D]
    {X Y U V : D} (i : X ≅ Y) (j : U ≅ V) (q : X ⟶ V) (s : V ⟶ X)
    (h : s ≫ q = 𝟙 V) :
    (j.hom ≫ s ≫ i.hom) ≫ (i.inv ≫ q ≫ j.inv) = 𝟙 U := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc s, h,
    Category.id_comp, Iso.hom_inv_id]

private theorem transport_projector {D : Type*} [Category D]
    {X Y U V : D} (i : X ≅ Y) (j : U ≅ V) (q : X ⟶ V) (s : V ⟶ X)
    (a : X ⟶ X) (h : q ≫ s = a) :
    (i.inv ≫ q ≫ j.inv) ≫ (j.hom ≫ s ≫ i.hom) = i.inv ≫ a ≫ i.hom := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc q, h]

private theorem summand_transport' {D : Type*} [Category D]
    {P Q A B C E : D} (p : P ⟶ A) (q : P ⟶ B)
    (u : A ⟶ B) (v : B ⟶ C) (w : C ⟶ E)
    (t : P ⟶ Q) (r : Q ⟶ C) (z : Q ⟶ E)
    (hp : p ≫ u = q) (hq : q ≫ v = t ≫ r) (hr : r ≫ w = z) :
    p ≫ (u ≫ v ≫ w) = t ≫ z := by
  rw [← Category.assoc, hp, ← Category.assoc, hq, Category.assoc, hr]

private theorem split_transport {R : Type*} [Semiring R]
    {D : Type*} [Category D] [Preadditive D] {X Y V W : D}
    (i : X ≅ Y) (j : V ≅ W) (a : R →+* End X) (q : X ⟶ W) (s : W ⟶ X)
    (e : R) (hsq : s ≫ q = 𝟙 W) (hqs : q ≫ s = a e) :
    ∃ (act : R →+* End Y) (bal : Y ⟶ V) (spl : V ⟶ Y),
      spl ≫ bal = 𝟙 V ∧ bal ≫ spl = act e ∧
      (∀ x, act x = i.inv ≫ a x ≫ i.hom) ∧ bal = i.inv ≫ q ≫ j.inv := by
  refine ⟨(conjugateEndRing i).comp a, i.inv ≫ q ≫ j.inv,
    j.hom ≫ s ≫ i.hom, transport_split i j q s hsq, ?_, ?_, rfl⟩
  · exact transport_projector i j q s (a e) hqs
  · intro x
    exact conjugateEndRing_apply i (a x)

end TensorTotalization

namespace TensorComparison
variable {A B D A' B' D' : Type u}
  [Category.{v} A] [Category.{v} B] [Category.{v} D]
  [Category.{v} A'] [Category.{v} B'] [Category.{v} D']
  [HasZeroMorphisms A] [HasZeroMorphisms B]
  [HasZeroMorphisms A'] [HasZeroMorphisms B']
  [Preadditive D] [Preadditive D'] [HasCoproducts.{0} D] [HasCoproducts.{0} D']
  {S : A ⥤ B ⥤ D} {R : A' ⥤ B' ⥤ D'}
  [S.PreservesZeroMorphisms] [∀ X, (S.obj X).PreservesZeroMorphisms]
  [R.PreservesZeroMorphisms] [∀ X, (R.obj X).PreservesZeroMorphisms]
  {U₁ : A ⥤ A'} {U₂ : B ⥤ B'} {U : D ⥤ D'}
  [U₁.PreservesZeroMorphisms] [U₂.PreservesZeroMorphisms]
  [U.Additive] [PreservesColimitsOfSize.{0, 0} U]
private noncomputable def comparison
    (τ : (Functor.postcompose₂.obj U).obj S ⟶
      (((Functor.whiskeringLeft₂ D').obj U₁).obj U₂).obj R) :
    Functor.uncurry.obj (S.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        U.mapHomologicalComplex (.up ℤ) ⟶
      ((U₁.mapHomologicalComplex (.up ℤ)).prod (U₂.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (R.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) where
  app KL := HomologicalComplex.mapBifunctorComparison τ (.up ℤ) KL.1 KL.2
  naturality KL KL' f := by
    dsimp only [Functor.comp_map, Functor.prod_map]
    rw [TensorTotalization.functor_map, TensorTotalization.functor_map]
    exact HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) f.1 f.2

private noncomputable def comparisonIso
    (τ : (Functor.postcompose₂.obj U).obj S ⟶
      (((Functor.whiskeringLeft₂ D').obj U₁).obj U₂).obj R)
    [hτ : ∀ X Y, IsIso ((τ.app X).app Y)] :
    Functor.uncurry.obj (S.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        U.mapHomologicalComplex (.up ℤ) ≅
      ((U₁.mapHomologicalComplex (.up ℤ)).prod (U₂.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (R.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) :=
  NatIso.ofComponents
    (fun KL ↦ asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) KL.1 KL.2))
    (fun f ↦ (comparison τ).naturality f)
@[reassoc] private theorem ι_comparisonIso
    (τ : (Functor.postcompose₂.obj U).obj S ⟶
      (((Functor.whiskeringLeft₂ D').obj U₁).obj U₂).obj R)
    [_hτ : ∀ X Y, IsIso ((τ.app X).app Y)]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    U.map (HomologicalComplex.ιMapBifunctor K L S (.up ℤ) i j n h) ≫
        (((comparisonIso τ).hom.app (K, L)).f n) =
      (τ.app (K.X i)).app (L.X j) ≫
        HomologicalComplex.ιMapBifunctor
          ((U₁.mapHomologicalComplex (.up ℤ)).obj K)
          ((U₂.mapHomologicalComplex (.up ℤ)).obj L) R (.up ℤ) i j n h :=
  HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) K L i j n h

private noncomputable def preIso
    {R : A' ⥤ B' ⥤ D} [R.PreservesZeroMorphisms]
    [∀ X, (R.obj X).PreservesZeroMorphisms]
    (τ : S ⟶ (((Functor.whiskeringLeft₂ D).obj U₁).obj U₂).obj R)
    [hτ : ∀ X Y, IsIso ((τ.app X).app Y)] :
    Functor.uncurry.obj (S.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      ((U₁.mapHomologicalComplex (.up ℤ)).prod (U₂.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (R.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) :=
  comparisonIso (U := 𝟭 D) (hτ := hτ) τ

@[reassoc] private theorem ι_preIso
    {R : A' ⥤ B' ⥤ D} [R.PreservesZeroMorphisms]
    [∀ X, (R.obj X).PreservesZeroMorphisms]
    (τ : S ⟶ (((Functor.whiskeringLeft₂ D).obj U₁).obj U₂).obj R)
    [hτ : ∀ X Y, IsIso ((τ.app X).app Y)]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L S (.up ℤ) i j n h ≫
        (((preIso τ).hom.app (K, L)).f n) =
      (τ.app (K.X i)).app (L.X j) ≫
        HomologicalComplex.ιMapBifunctor
          ((U₁.mapHomologicalComplex (.up ℤ)).obj K)
          ((U₂.mapHomologicalComplex (.up ℤ)).obj L) R (.up ℤ) i j n h :=
  ι_comparisonIso (U := 𝟭 D) (_hτ := hτ) τ K L i j n h

private noncomputable def postIso
    {R : A ⥤ B ⥤ D'} [R.PreservesZeroMorphisms]
    [∀ X, (R.obj X).PreservesZeroMorphisms]
    (τ : (Functor.postcompose₂.obj U).obj S ⟶ R)
    [hτ : ∀ X Y, IsIso ((τ.app X).app Y)] :
    Functor.uncurry.obj (S.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        U.mapHomologicalComplex (.up ℤ) ≅
      Functor.uncurry.obj (R.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) :=
  comparisonIso (U₁ := 𝟭 _) (U₂ := 𝟭 _) (hτ := hτ) τ

@[reassoc] private theorem ι_postIso
    {R : A ⥤ B ⥤ D'} [R.PreservesZeroMorphisms]
    [∀ X, (R.obj X).PreservesZeroMorphisms]
    (τ : (Functor.postcompose₂.obj U).obj S ⟶ R)
    [hτ : ∀ X Y, IsIso ((τ.app X).app Y)]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    U.map (HomologicalComplex.ιMapBifunctor K L S (.up ℤ) i j n h) ≫
        (((postIso τ).hom.app (K, L)).f n) =
      (τ.app (K.X i)).app (L.X j) ≫
        HomologicalComplex.ιMapBifunctor K L R (.up ℤ) i j n h :=
  ι_comparisonIso (U₁ := 𝟭 _) (U₂ := 𝟭 _) (_hτ := hτ) τ K L i j n h

private theorem inverse_equation {D : Type*} [Category D]
    {W X Y : D} (i : X ≅ Y) {a : W ⟶ X} {b : W ⟶ Y}
    (h : a ≫ i.hom = b) : b ≫ i.inv = a := by
  rw [← h, Category.assoc, i.hom_inv_id, Category.comp_id]

end TensorComparison

namespace TensorRetraction
variable {A D E : Type u} [Category.{v} A] [Category.{v} D] [Category.{v} E]
  [HasZeroMorphisms A] [Preadditive D] [Preadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]

private noncomputable def preTensor (U : A ⥤ D) (F : D ⥤ D ⥤ D) : A ⥤ A ⥤ D :=
  (((Functor.whiskeringLeft₂ D).obj U).obj U).obj F

private noncomputable def postTensor (V : E ⥤ D) (G : A ⥤ A ⥤ E) : A ⥤ A ⥤ D :=
  (Functor.postcompose₂.obj V).obj G

omit [HasCoproducts D] [HasCoproducts E] in
private theorem preTensor_preservesZeroMorphisms (U : A ⥤ D) (F : D ⥤ D ⥤ D)
    [U.PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
    [∀ M : D, (F.obj M).PreservesZeroMorphisms] :
    (preTensor U F).PreservesZeroMorphisms := ⟨by
  intro M N
  apply NatTrans.ext
  funext P
  change ((F.map (U.map 0)).app (U.obj P)) = 0
  simp only [Functor.map_zero, NatTrans.app_zero]⟩

omit [HasCoproducts D] [HasCoproducts E] in
private theorem preTensor_obj_preservesZeroMorphisms (U : A ⥤ D) (F : D ⥤ D ⥤ D)
    [U.PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
    [∀ M : D, (F.obj M).PreservesZeroMorphisms] (M : A) :
    ((preTensor U F).obj M).PreservesZeroMorphisms := by
  change (U ⋙ F.obj (U.obj M)).PreservesZeroMorphisms
  infer_instance

omit [HasCoproducts D] [HasCoproducts E] in
private theorem postTensor_preservesZeroMorphisms (V : E ⥤ D) (G : A ⥤ A ⥤ E)
    [V.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [∀ M : A, (G.obj M).PreservesZeroMorphisms] :
    (postTensor V G).PreservesZeroMorphisms := ⟨by
  intro M N
  apply NatTrans.ext
  funext P
  change V.map ((G.map 0).app P) = 0
  simp only [Functor.map_zero, NatTrans.app_zero]⟩

omit [HasCoproducts D] [HasCoproducts E] in
private theorem postTensor_obj_preservesZeroMorphisms (V : E ⥤ D) (G : A ⥤ A ⥤ E)
    [V.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [∀ M : A, (G.obj M).PreservesZeroMorphisms] (M : A) :
    ((postTensor V G).obj M).PreservesZeroMorphisms := by
  change (G.obj M ⋙ V).PreservesZeroMorphisms
  infer_instance

private noncomputable abbrev lifted {A B D : Type u}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
    (F : A ⥤ B ⥤ D) [h₁ : F.PreservesZeroMorphisms]
    [h₂ : ∀ X : A, (F.obj X).PreservesZeroMorphisms] :=
  CochainTensorBifunctor.rawFunctor F

private abbrev complexMap {A D : Type u} [Category.{v} A] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms D] (U : A ⥤ D)
    [hzero : U.PreservesZeroMorphisms] : CochainComplex A ℤ ⥤ CochainComplex D ℤ :=
  U.mapHomologicalComplex (.up ℤ)

private noncomputable def inclusion {A B D : Type u}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
    (F : A ⥤ B ⥤ D) [h₁ : F.PreservesZeroMorphisms]
    [h₂ : ∀ X : A, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    (F.obj (K.X i)).obj (L.X j) ⟶
      ((lifted (h₁ := h₁) (h₂ := h₂) F).obj (K, L)).X n :=
  HomologicalComplex.ιMapBifunctor K L F (.up ℤ) i j n h

set_option backward.isDefEq.respectTransparency false in
/-- Totalization preserves a split bifunctor action and its summand equations. -/
private theorem split_totalization
    (F : D ⥤ D ⥤ D) (G : A ⥤ A ⥤ E) (U : A ⥤ D) (V : E ⥤ D)
    [hf₁ : F.PreservesZeroMorphisms] [hf₂ : ∀ X : D, (F.obj X).PreservesZeroMorphisms]
    [hg₁ : G.PreservesZeroMorphisms] [hg₂ : ∀ X : A, (G.obj X).PreservesZeroMorphisms]
    [hu : U.PreservesZeroMorphisms] [V.Additive] [hvzero : V.PreservesZeroMorphisms]
    [PreservesColimitsOfSize.{0, 0} V]
    {R₀ : Type w} [Semiring R₀]
    (a : R₀ →+* End (preTensor U F))
    (q : preTensor U F ⟶ postTensor V G) (s : postTensor V G ⟶ preTensor U F)
    (e : R₀) (hsq : s ≫ q = 𝟙 _) (hqs : q ≫ s = a e) :
    ∃ (act : R₀ →+* End
        (((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ lifted (h₁ := hf₁) (h₂ := hf₂) F))
      (bal : ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ lifted (h₁ := hf₁) (h₂ := hf₂) F ⟶
        lifted (h₁ := hg₁) (h₂ := hg₂) G ⋙ complexMap (hzero := hvzero) V)
      (spl : lifted (h₁ := hg₁) (h₂ := hg₂) G ⋙ complexMap (hzero := hvzero) V ⟶
        ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ lifted (h₁ := hf₁) (h₂ := hf₂) F),
      spl ≫ bal = 𝟙 _ ∧ bal ≫ spl = act e ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) (x : R₀),
        inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            ((act x).app (K, L)).f n =
          ((a x).app (K.X i)).app (L.X j) ≫
            inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h) ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n),
        inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            (bal.app (K, L)).f n =
          (q.app (K.X i)).app (L.X j) ≫
            V.map (inclusion (h₁ := hg₁) (h₂ := hg₂) G K L i j n h)) := by
  let hpre₁ := preTensor_preservesZeroMorphisms U F
  let hpre₂ := preTensor_obj_preservesZeroMorphisms U F
  let hpost₁ := postTensor_preservesZeroMorphisms V G
  let hpost₂ := postTensor_obj_preservesZeroMorphisms V G
  let T := lifted (h₁ := hpre₁) (h₂ := hpre₂) (preTensor U F)
  let W := lifted (h₁ := hpost₁) (h₂ := hpost₂) (postTensor V G)
  let τF : preTensor U F ⟶
      (((Functor.whiskeringLeft₂ D).obj U).obj U).obj
        (F) := 𝟙 _
  let hτF (M N : A) : IsIso ((τF.app M).app N) :=
    inferInstanceAs (IsIso (𝟙 _))
  let iF : T ≅ ((complexMap (hzero := hu) U).prod
      (complexMap (hzero := hu) U)) ⋙ lifted (h₁ := hf₁) (h₂ := hf₂) F :=
    TensorComparison.preIso
      (S := preTensor U F)
      (R := F)
      (U₁ := U) (U₂ := U) (hτ := hτF) τF
  let τ : postTensor V G ⟶ postTensor V G := 𝟙 _
  let hτ (M N : A) : IsIso ((τ.app M).app N) :=
    inferInstanceAs (IsIso (𝟙 _))
  let iB : lifted (h₁ := hg₁) (h₂ := hg₂) G ⋙ complexMap (hzero := hvzero) V ≅ W :=
    TensorComparison.postIso
      (S := G)
      (R := postTensor V G) (U := V) (hτ := hτ) τ
  have hF (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) :
      inclusion (h₁ := hpre₁) (h₂ := hpre₂) (preTensor U F) K L i j n h ≫
        (iF.hom.app (K, L)).f n =
      inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h := by
    have hh := TensorComparison.ι_preIso (hτ := hτF) τF K L i j n h
    dsimp only [τF, NatTrans.id_app, Functor.id_map] at hh
    erw [Category.id_comp] at hh
    exact hh
  clear_value iF
  have hFi (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) :
      inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
        (iF.inv.app (K, L)).f n =
      inclusion (h₁ := hpre₁) (h₂ := hpre₂) (preTensor U F) K L i j n h := by
    exact TensorComparison.inverse_equation
      ((HomologicalComplex.eval D (.up ℤ) n).mapIso (iF.app (K, L))) (hF K L i j n h)
  have hBt (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) :
      V.map (inclusion (h₁ := hg₁) (h₂ := hg₂) G K L i j n h) ≫
        (iB.hom.app (K, L)).f n =
      inclusion (h₁ := hpost₁) (h₂ := hpost₂) (postTensor V G) K L i j n h := by
    have hh := TensorComparison.ι_postIso (hτ := hτ) τ K L i j n h
    dsimp only [τ, NatTrans.id_app] at hh
    erw [Category.id_comp] at hh
    exact hh
  clear_value iB
  have hBi (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) :
      inclusion (h₁ := hpost₁) (h₂ := hpost₂) (postTensor V G) K L i j n h ≫
        (iB.inv.app (K, L)).f n =
      V.map (inclusion (h₁ := hg₁) (h₂ := hg₂) G K L i j n h) := by
    exact TensorComparison.inverse_equation
      ((HomologicalComplex.eval D (.up ℤ) n).mapIso (iB.app (K, L))) (hBt K L i j n h)
  let aa : R₀ →+* End T := (TensorTotalization.ringHom (F := preTensor U F)).comp a
  let qq : T ⟶ W := TensorTotalization.natTrans q
  let ss : W ⟶ T := TensorTotalization.natTrans s
  have hss : ss ≫ qq = 𝟙 W := by
    rw [← TensorTotalization.natTrans_comp, hsq, TensorTotalization.natTrans_id]
    rfl
  have hqq : qq ≫ ss = aa e := by
    rw [← TensorTotalization.natTrans_comp, hqs]
    rfl
  obtain ⟨act, bal, spl, hsbal, hbals, hact, hbal⟩ :=
    TensorTotalization.split_transport iF iB aa qq ss e hss hqq
  have hActι (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n)
      (x : R₀) :
      inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
        ((act x).app (K, L)).f n =
      ((a x).app (K.X i)).app (L.X j) ≫
        inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h := by
    rw [hact]
    change _ ≫ ((iF.inv.app (K, L)).f n ≫
      (TensorTotalization.map (a x) K L).f n ≫ (iF.hom.app (K, L)).f n) = _
    exact TensorTotalization.summand_transport' _ _ _ _ _ _ _ _
      (hFi K L i j n h) (TensorTotalization.ι_map (a x) K L i j n h)
      (hF K L i j n h)
  have hBalι (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) :
      inclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
        (bal.app (K, L)).f n =
      (q.app (K.X i)).app (L.X j) ≫
        V.map (inclusion (h₁ := hg₁) (h₂ := hg₂) G K L i j n h) := by
    rw [hbal]
    change _ ≫ ((iF.inv.app (K, L)).f n ≫
      (TensorTotalization.map q K L).f n ≫ (iB.inv.app (K, L)).f n) = _
    exact TensorTotalization.summand_transport' _ _ _ _ _ _ _ _
      (hFi K L i j n h) (TensorTotalization.ι_map q K L i j n h)
      (hBi K L i j n h)
  exact ⟨act, bal, spl, hsbal, hbals, hActι, hBalι⟩

private noncomputable abbrev modelLifted {A B D : Type u}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
    (F : A ⥤ B ⥤ D) [h₁ : F.PreservesZeroMorphisms]
    [h₂ : ∀ X : A, (F.obj X).PreservesZeroMorphisms] :=
  CochainTensorBifunctor.totalFunctor F

private noncomputable def modelInclusion {A B D : Type u}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
    (F : A ⥤ B ⥤ D) [h₁ : F.PreservesZeroMorphisms]
    [h₂ : ∀ X : A, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    (F.obj (K.X i)).obj (L.X j) ⟶
      ((modelLifted (h₁ := h₁) (h₂ := h₂) F).obj (K, L)).X n :=
  CochainTensorBifunctor.inclusion F K L i j n h

/-- Parameterizing the whole model keeps dependent ring instances under equality transport. -/
private def HasModelRetraction
    (F : D ⥤ D ⥤ D) (G : A ⥤ A ⥤ E) (U : A ⥤ D) (V : E ⥤ D)
    (MF : CochainTensorBifunctor.Model F) (MG : CochainTensorBifunctor.Model G)
    [hu : U.PreservesZeroMorphisms] [hvzero : V.PreservesZeroMorphisms]
    {R₀ : Type w} [Semiring R₀]
    (a : R₀ →+* End (preTensor U F)) (q : preTensor U F ⟶ postTensor V G)
    (e : R₀) : Prop :=
    ∃ (act : R₀ →+* End
        (((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ MF.functor))
      (bal : ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ MF.functor ⟶
        MG.functor ⋙ complexMap (hzero := hvzero) V)
      (spl : MG.functor ⋙ complexMap (hzero := hvzero) V ⟶
        ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ MF.functor),
      spl ≫ bal = 𝟙 _ ∧ bal ≫ spl = act e ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) (x : R₀),
        MF.inclusion
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            ((act x).app (K, L)).f n =
          ((a x).app (K.X i)).app (L.X j) ≫
            MF.inclusion
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h) ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n),
        MF.inclusion
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            (bal.app (K, L)).f n =
          (q.app (K.X i)).app (L.X j) ≫
            V.map (MG.inclusion K L i j n h))

private theorem split_totalization_model
    (F : D ⥤ D ⥤ D) (G : A ⥤ A ⥤ E) (U : A ⥤ D) (V : E ⥤ D)
    [hf₁ : F.PreservesZeroMorphisms] [hf₂ : ∀ X : D, (F.obj X).PreservesZeroMorphisms]
    [hg₁ : G.PreservesZeroMorphisms] [hg₂ : ∀ X : A, (G.obj X).PreservesZeroMorphisms]
    [hu : U.PreservesZeroMorphisms] [V.Additive] [hvzero : V.PreservesZeroMorphisms]
    [PreservesColimitsOfSize.{0, 0} V]
    {R₀ : Type w} [Semiring R₀]
    (a : R₀ →+* End (preTensor U F))
    (q : preTensor U F ⟶ postTensor V G) (s : postTensor V G ⟶ preTensor U F)
    (e : R₀) (hsq : s ≫ q = 𝟙 _) (hqs : q ≫ s = a e) :
    ∃ (act : R₀ →+* End
        (((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ modelLifted (h₁ := hf₁) (h₂ := hf₂) F))
      (bal : ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ modelLifted (h₁ := hf₁) (h₂ := hf₂) F ⟶
        modelLifted (h₁ := hg₁) (h₂ := hg₂) G ⋙ complexMap (hzero := hvzero) V)
      (spl : modelLifted (h₁ := hg₁) (h₂ := hg₂) G ⋙ complexMap (hzero := hvzero) V ⟶
        ((complexMap (hzero := hu) U).prod
          (complexMap (hzero := hu) U)) ⋙ modelLifted (h₁ := hf₁) (h₂ := hf₂) F),
      spl ≫ bal = 𝟙 _ ∧ bal ≫ spl = act e ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n) (x : R₀),
        modelInclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            ((act x).app (K, L)).f n =
          ((a x).app (K.X i)).app (L.X j) ≫
            modelInclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h) ∧
      (∀ (K L : CochainComplex A ℤ) (i j n : ℤ) (h : i + j = n),
        modelInclusion (h₁ := hf₁) (h₂ := hf₂) F
          ((complexMap (hzero := hu) U).obj K)
          ((complexMap (hzero := hu) U).obj L) i j n h ≫
            (bal.app (K, L)).f n =
          (q.app (K.X i)).app (L.X j) ≫
            V.map (modelInclusion (h₁ := hg₁) (h₂ := hg₂) G K L i j n h)) := by
  change HasModelRetraction F G U V
    (CochainTensorBifunctor.model F) (CochainTensorBifunctor.model G) a q e
  rw [CochainTensorBifunctor.model_eq F, CochainTensorBifunctor.model_eq G]
  exact split_totalization F G U V a q s e hsq hqs

end TensorRetraction

private theorem map_section_of_comp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N P Q : SheafOfModules R}
    (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ P) (d : P ⟶ Q)
    (X : Cᵒᵖ) (m : M.val.obj X) (z : P.val.obj X)
    (hsq : a ≫ b = c ≫ d) (hz : c.val.app X m = z) :
    b.val.app X (a.val.app X m) = d.val.app X z := by
  have h := congrArg (fun f : M ⟶ Q ↦ f.val.app X m) hsq
  exact h.trans (congrArg (fun t ↦ d.val.app X t) hz)

namespace FiniteFieldDerivedTensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v}]
  (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]

attribute [local irreducible] coefficientMap SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
private noncomputable def totalInclusion (A : Type (max u v)) [CommRing A]
    (K L : Complexes J A) (i j n : ℤ) (h : i + j = n) :
    ((tensorFunctor J A).obj (K.X i)).obj (L.X j) ⟶
      ((total J A).obj (K, L)).X n :=
  TensorRetraction.modelInclusion (tensorFunctor J A) K L i j n h

set_option backward.isDefEq.respectTransparency true in
private theorem generator_eq (A : Type (max u v)) [CommRing A]
    (K L : Complexes J A) (i j : ℤ) (X : Cᵒᵖ)
    (m : (K.X i).val.obj X) (n : (L.X j).val.obj X) :
    generator J A K L i j X m n =
      (totalInclusion J A K L i j (i + j) rfl).val.app X
        (tensorSection J A (K.X i) (L.X j) X m n) := rfl

set_option backward.isDefEq.respectTransparency true in
private theorem map_generator (K L T : Complexes J F)
    (p : (total J F).obj (K, L) ⟶ T) (i j : ℤ) (X : Cᵒᵖ)
    (m : (K.X i).val.obj X) (n : (L.X j).val.obj X)
    (D : Modules J F) (ι : D ⟶ T.X (i + j))
    (r : ((tensorFunctor J F).obj (K.X i)).obj (L.X j) ⟶ D)
    (z : D.val.obj X)
    (hι : totalInclusion J F K L i j (i + j) rfl ≫
        p.f (i + j) = r ≫ ι)
    (hz : r.val.app X (tensorSection J F (K.X i) (L.X j) X m n) = z) :
    (p.f (i + j)).val.app X (generator J F K L i j X m n) = ι.val.app X z := by
  rw [generator_eq]
  exact map_section_of_comp
    (totalInclusion J F K L i j (i + j) rfl) (p.f (i + j)) r ι X
    (tensorSection J F (K.X i) (L.X j) X m n) z hι hz

-- Keep the chosen totalization coproducts folded during specialization.
attribute [local irreducible] CochainTensorBifunctor.totalFunctor

private def IsTensorActionOnSummands
    (a : (B ⊗[F] B) →+* End (sheafSource J F B))
    (act : (B ⊗[F] B) →+* End
      (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F)) : Prop :=
  ∀ (K L : Complexes J B) (i j n : ℤ) (h : i + j = n)
      (x : B ⊗[F] B),
      totalInclusion J F ((restrictComplex J F B).obj K)
          ((restrictComplex J F B).obj L) i j n h ≫
        ((act x).app (K, L)).f n =
      ((a x).app (K.X i)).app (L.X j) ≫
        totalInclusion J F ((restrictComplex J F B).obj K)
          ((restrictComplex J F B).obj L) i j n h

private def IsBalancedOnSummands
    (q : sheafSource J F B ⟶ sheafTarget J F B)
    (bal : ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
      total J B ⋙ restrictComplex J F B) : Prop :=
  ∀ (K L : Complexes J B) (i j n : ℤ) (h : i + j = n),
      totalInclusion J F ((restrictComplex J F B).obj K)
          ((restrictComplex J F B).obj L) i j n h ≫
        (bal.app (K, L)).f n =
      (q.app (K.X i)).app (L.X j) ≫
        (SheafOfModules.restrictScalars (coefficientMap J F B)).map
          (totalInclusion J B K L i j n h)

section ChainConstructor
attribute [local irreducible] total tensorSection generator constantSection

set_option backward.isDefEq.respectTransparency false in
private theorem chain_of_summands
    (a : (B ⊗[F] B) →+* End (sheafSource J F B))
    (q : sheafSource J F B ⟶ sheafTarget J F B)
    (act : (B ⊗[F] B) →+* End
      (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F))
    (bal : ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
      total J B ⋙ restrictComplex J F B)
    (ha : IsSheafTensorAction J F B a)
    (hq : IsSheafBalancedMap J F B q)
    (hActι : IsTensorActionOnSummands J F B a act)
    (hBalι : IsBalancedOnSummands J F B q bal)
    : ∃ chain : ChainComparison (J := J) (F := F) (B := B),
      chain.chainBalanced = bal ∧ ∀ (K L : Complexes J B) (x : B ⊗[F] B),
        (act x).app (K, L) = chain.chainAction K L x := by
  set_option backward.isDefEq.respectTransparency true in
    let U := SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)
    let action (K L : Complexes J B) : (B ⊗[F] B) →+*
        End ((total J F).obj
          ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L)) :=
      (TensorTotalization.evaluationRingHom
        (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F) (K, L)).comp act
    have hAction (K L : Complexes J B) (x : B ⊗[F] B) :
        action K L x = (act x).app (K, L) := by
      change TensorTotalization.evaluationRingHom
        (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F) (K, L)
          (act x) = _
      exact TensorTotalization.evaluationRingHom_apply _ _ _
    clear_value action
    let chain : ChainComparison (J := J) (F := F) (B := B) :=
      { chainAction := action
        chainBalanced := bal
        action_generator := by
          intro K L b c i j X m n
          rw [hAction]
          exact (map_generator J F
            ((restrictComplex J F B).obj K) ((restrictComplex J F B).obj L)
            ((total J F).obj ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L))
            ((act (b ⊗ₜ[F] c)).app (K, L)) i j X m n
            (((sheafSource J F B).obj (K.X i)).obj (L.X j))
            (totalInclusion J F ((restrictComplex J F B).obj K)
            ((restrictComplex J F B).obj L) i j (i + j) rfl)
            (((a (b ⊗ₜ[F] c)).app (K.X i)).app (L.X j)) _
            (hActι K L i j (i + j) rfl (b ⊗ₜ[F] c))
            (ha (K.X i) (L.X j) b c X m n)).trans
            (generator_eq J F ((restrictComplex J F B).obj K)
              ((restrictComplex J F B).obj L) i j X
              _ _).symm
        balanced_generator := by
          intro K L i j X m n
          exact (map_generator J F
            ((restrictComplex J F B).obj K) ((restrictComplex J F B).obj L)
            ((restrictComplex J F B).obj ((total J B).obj (K, L)))
            (bal.app (K, L)) i j X m n
            (((sheafTarget J F B).obj (K.X i)).obj (L.X j))
            (U.map (totalInclusion J B K L i j (i + j) rfl))
            ((q.app (K.X i)).app (L.X j)) _
            (hBalι K L i j (i + j) rfl) (hq (K.X i) (L.X j) X m n)).trans
            (generator_eq J B K L i j X m n).symm }
    exact ⟨chain, rfl, fun K L x ↦ (hAction K L x).symm⟩

end ChainConstructor

private theorem chain_retraction_of_summands
    (a : (B ⊗[F] B) →+* End (sheafSource J F B))
    (q : sheafSource J F B ⟶ sheafTarget J F B)
    (e : B ⊗[F] B)
    (ha : IsSheafTensorAction J F B a) (hq : IsSheafBalancedMap J F B q)
    (h : ∃ (act : (B ⊗[F] B) →+* End
        (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F))
      (bal : ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
        total J B ⋙ restrictComplex J F B)
      (spl : total J B ⋙ restrictComplex J F B ⟶
        ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F),
      spl ≫ bal = 𝟙 _ ∧ bal ≫ spl = act e ∧
      IsTensorActionOnSummands J F B a act ∧ IsBalancedOnSummands J F B q bal) :
    ∃ (chain : ChainComparison (J := J) (F := F) (B := B))
      (a : (B ⊗[F] B) →+* End
        (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F))
      (s : total J B ⋙ restrictComplex J F B ⟶
        ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F),
      s ≫ chain.chainBalanced = 𝟙 _ ∧
      chain.chainBalanced ≫ s = a e ∧
      ∀ (K L : Complexes J B) (x : B ⊗[F] B),
        (a x).app (K, L) = chain.chainAction K L x := by
  obtain ⟨act, bal, spl, hsbal, hbals, hAct, hBal⟩ := h
  obtain ⟨chain, hchain, hchainact⟩ :=
    chain_of_summands J F B a q act bal ha hq hAct hBal
  exact ⟨chain, act, spl,
    (congrArg (fun f ↦ spl ≫ f) hchain).trans hsbal,
    (congrArg (fun f ↦ f ≫ spl) hchain).trans hbals, hchainact⟩

set_option backward.isDefEq.respectTransparency true in
/-- A separability element splits the balanced quotient of total sheaf tensors.
Source: Stacks Project, Tag 0C2X, diagonal idempotent; Tags 03EK and 0GMW,
tensor universal property; Tag 06YU, total tensor complexes
(blueprint: lem-pur-separable-field-tensor-chain).
Proof: On a pure tensor the two coefficient actions send m tensor n to a m tensor b n.
Their actions commute and agree on F, so the tensor-ring universal property gives a
ring homomorphism into natural endomorphisms. The balanced quotient sends m tensor_F n
to m tensor_B n. Write e as a finite sum of pure tensors a_i tensor b_i. Define its
section by m tensor_B n mapping to the sum of a_i m tensor_F b_i n. The identities
(b tensor 1 minus 1 tensor b)e = 0 prove B-balancing; multiplication(e) = 1 proves
that quotient after section is the identity. Section after quotient is the action of e.
First make these maps on modules over the constant presheaves. Extend the bilinear maps
through module sheafification using Tag 0GMW; uniqueness proves both identities and
naturality, including sections of the constant sheaf which are only locally constant.
Apply the maps in every bidegree. Coefficient-linear differentials commute with them,
so taking direct sums along integer diagonals gives chain maps. The two identities
hold on each summand and hence on the total. The same calculation proves the specified
pure-generator formulas. No boundedness, nonzero section, or nonempty site is required. -/
theorem exists_separableFieldTensorChain (e : B ⊗[F] B)
    (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (he : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    ∃ (chain : ChainComparison (J := J) (F := F) (B := B))
      (a : (B ⊗[F] B) →+* End
        (((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F))
      (s : total J B ⋙ restrictComplex J F B ⟶
        ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F),
      s ≫ chain.chainBalanced = 𝟙 _ ∧
      chain.chainBalanced ≫ s = a e ∧
      ∀ (K L : Complexes J B) (x : B ⊗[F] B),
        (a x).app (K, L) = chain.chainAction K L x := by
  obtain ⟨a, q, s, hsq, hqs, ha, hq⟩ := exists_separableFieldTensorSheaf J F B e hμ he
  let U := SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)
  have hcol : PreservesColimitsOfSize.{0, 0} U :=
    restrictScalars_preservesSmallColimits (coefficientMap J F B)
  apply chain_retraction_of_summands J F B a q e ha hq
  exact TensorRetraction.split_totalization_model
      (tensorFunctor J F)
      (tensorFunctor J B)
      U U
      a q s e hsq hqs

end FiniteFieldDerivedTensor
