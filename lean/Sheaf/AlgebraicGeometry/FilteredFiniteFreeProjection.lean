module

public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityCoefficientRestriction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Filtered finite-free projection

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), equation (5.4), and Stacks Tags
0B56, 0944, 03DB, 03EP (blueprint: lem-sfb-filtered-finite-free-projection).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory SheafOfModules

private theorem tensorMateNaturality
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (G : B ⥤ A) (adj : L ⊣ G)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (mu : T ⋙ L ⟶ (L.prod L) ⋙ U) (Z : B)
    {P Q : A} (v : P ⟶ Q) :
    T.map (Prod.mkHom v (𝟙 (G.obj Z))) ≫
        adj.homEquiv _ _ (mu.app (Q, G.obj Z) ≫
          U.map (Prod.mkHom (𝟙 (L.obj Q)) (adj.counit.app Z))) =
      adj.homEquiv _ _ (mu.app (P, G.obj Z) ≫
          U.map (Prod.mkHom (𝟙 (L.obj P)) (adj.counit.app Z))) ≫
        G.map (U.map (Prod.mkHom (L.map v) (𝟙 Z))) := by
  apply adj.homEquiv_naturality_left_square
  have h := mu.naturality (Prod.mkHom v (𝟙 (G.obj Z)))
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext <;> simp

private theorem uncurryMapRightId
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ B ⥤ D) {M N : A} (v : M ⟶ N) (K : B) :
    (Functor.uncurry.obj F).map (Prod.mkHom v (𝟙 K)) = (F.map v).app K := by
  change (F.map v).app K ≫ (F.obj N).map (𝟙 K) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private def fixedTensorIso
    {A B : Type*} [Category A] [Category B]
    (T U : A × A ⥤ B) (z : T ≅ U) {K D : A} (e : K ≅ D) :
    (Functor.curryObj T).flip.obj K ≅ (Functor.curryObj U).flip.obj D :=
  (Functor.curryObj T).flip.mapIso e ≪≫
    ((flipFunctor _ _ _).mapIso (Functor.curry.mapIso z)).app D

private theorem tensorComparisonNaturality
    {D E : Type*} [Category D] [Category E]
    (T U : D × D ⥤ E) (z : T ≅ U)
    {X Y X' Y' K C : D} {V W : E}
    (r : V ≅ T.obj (X, K)) (s : W ≅ T.obj (Y, K))
    (x : X ≅ X') (y : Y ≅ Y') (e : K ≅ C)
    (f : V ⟶ W) (g : X ⟶ Y) (h : X' ⟶ Y')
    (hr : f ≫ s.hom = r.hom ≫ T.map (Prod.mkHom g (𝟙 K)))
    (hx : g ≫ y.hom = x.hom ≫ h) :
    f ≫ (s ≪≫ z.app (Y, K) ≪≫ U.mapIso (Iso.prod y e)).hom =
      (r ≪≫ z.app (X, K) ≪≫ U.mapIso (Iso.prod x e)).hom ≫
        U.map (Prod.mkHom h (𝟙 C)) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hr, Category.assoc]
  simp only [Category.assoc, Iso.app_hom]
  rw [z.hom.naturality_assoc]
  rw [← U.map_comp, ← U.map_comp]
  apply congrArg (r.hom ≫ ·)
  apply congrArg (z.hom.app (X, K) ≫ ·)
  apply U.congr_map
  ext
  · exact hx
  · simp

private theorem unitMateIsIso
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (G : B ⥤ A) (adj : L ⊣ G)
    (H : A ⥤ A) (K : B ⥤ B) (h : H ≅ 𝟭 A) (k : K ≅ 𝟭 B)
    (mu : H ⋙ L ≅ L ⋙ K) (Z : B) :
    IsIso (adj.homEquiv _ _ (mu.hom.app (G.obj Z) ≫ K.map (adj.counit.app Z))) := by
  let alpha : L ≅ L :=
    (Functor.leftUnitor L).symm ≪≫ Functor.isoWhiskerRight h.symm L ≪≫ mu ≪≫
      Functor.isoWhiskerLeft L k ≪≫ Functor.rightUnitor L
  let z := conjugateIsoEquiv adj adj alpha
  have hc : adj.homEquiv _ _ (alpha.hom.app (G.obj Z) ≫ adj.counit.app Z) =
      z.hom.app Z := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (conjugateEquiv_counit adj adj alpha.hom Z).symm
  have hm : adj.homEquiv _ _ (mu.hom.app (G.obj Z) ≫ K.map (adj.counit.app Z)) ≫
      G.map (k.hom.app Z) = h.hom.app (G.obj Z) ≫ z.hom.app Z := by
    rw [← hc]
    apply (adj.homEquiv _ _).symm.injective
    simp only [adj.homEquiv_naturality_right_symm,
      adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    change (mu.hom.app (G.obj Z) ≫ K.map (adj.counit.app Z)) ≫ k.hom.app Z =
      L.map (h.hom.app (G.obj Z)) ≫ (adj.homEquiv (G.obj Z) Z).symm
        ((adj.homEquiv (G.obj Z) Z) (alpha.hom.app (G.obj Z) ≫ adj.counit.app Z))
    rw [Equiv.symm_apply_apply]
    simp only [alpha, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.id_comp]
    simp only [← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id,
      Category.id_comp, Category.assoc]
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map]
    rw [Category.id_comp]
    exact congrArg (fun t ↦ mu.hom.app (G.obj Z) ≫ t)
      (k.hom.naturality (adj.counit.app Z))
  have : IsIso (adj.homEquiv _ _
      (mu.hom.app (G.obj Z) ≫ K.map (adj.counit.app Z)) ≫ G.map (k.hom.app Z)) := by
    rw [hm]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (k.hom.app Z))

private def curryTensorIso (A : Type*) [Category A] [MonoidalCategory A] :
    Functor.curryObj (MonoidalCategory.tensor A) ≅ MonoidalCategory.curriedTensor A :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _) (by
    intro Y Z g
    simp [Functor.curryObj, MonoidalCategory.tensor, MonoidalCategory.curriedTensor])) (by
      intro X Y f
      ext Z
      simp [Functor.curryObj, MonoidalCategory.tensor, MonoidalCategory.curriedTensor])

private theorem fixedTensorAdditiveOfIso
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    (T : A × A ⥤ A) (C : A) (e : MonoidalCategory.tensor A ≅ T)
    [((MonoidalCategory.curriedTensor A).flip.obj C).Additive] :
    ((Functor.curryObj T).flip.obj C).Additive := by
  let e' := (curryTensorIso A).symm ≪≫ Functor.curry.mapIso e
  let z : (MonoidalCategory.curriedTensor A).flip.obj C ≅
      (Functor.curryObj T).flip.obj C := ((flipFunctor _ _ _).mapIso e').app C
  exact Functor.additive_of_iso z

private theorem colimitDescNaturality
    {A B : Type*} [Category A] [Category B] {I : Type*} [Category I]
    (P : I ⥤ A) (v : Cocone P) (F G : A ⥤ B) (t : F ⟶ G)
    [HasColimit (P ⋙ F)] [HasColimit (P ⋙ G)] :
    colimit.desc (P ⋙ F) (F.mapCocone v) ≫ t.app v.pt =
      colimMap (Functor.whiskerLeft P t) ≫ colimit.desc (P ⋙ G) (G.mapCocone v) := by
  apply colimit.hom_ext
  intro i
  simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc,
    Functor.whiskerLeft_app, Functor.mapCocone_ι_app]
  exact t.naturality (v.ι.app i)

private theorem isIsoAppOfColimitDesc
    {A B : Type*} [Category A] [Category B] {I : Type*} [Category I]
    (P : I ⥤ A) (v : Cocone P) (F G : A ⥤ B) (t : F ⟶ G)
    [HasColimit (P ⋙ F)] [HasColimit (P ⋙ G)]
    [IsIso (colimit.desc (P ⋙ F) (F.mapCocone v))]
    [IsIso (colimit.desc (P ⋙ G) (G.mapCocone v))]
    (ht : ∀ i, IsIso (t.app (P.obj i))) : IsIso (t.app v.pt) := by
  have : IsIso (Functor.whiskerLeft P t) :=
    @NatIso.isIso_of_isIso_app I _ B _ (P ⋙ F) (P ⋙ G)
      (Functor.whiskerLeft P t) ht
  have hright : IsIso (colimMap (Functor.whiskerLeft P t) ≫
      colimit.desc (P ⋙ G) (G.mapCocone v)) := inferInstance
  have : IsIso (colimit.desc (P ⋙ F) (F.mapCocone v) ≫ t.app v.pt) :=
    (colimitDescNaturality P v F G t).symm ▸ hright
  exact IsIso.of_isIso_comp_left (colimit.desc (P ⋙ F) (F.mapCocone v)) _

@[irreducible] private def mapCoproductIso
    {A B : Type*} [Category A] [Category B] (L : A ⥤ B)
    {J : Type*} (U : J → A) (V : J → B)
    [HasCoproduct U] [HasCoproductsOfShape J B]
    [PreservesColimit (Discrete.functor U) L]
    {M : A} (e : M ≅ ∐ U) (j : ∀ i, L.obj (U i) ≅ V i) :
    L.obj M ≅ ∐ V :=
  L.mapIso e ≪≫ PreservesCoproduct.iso L U ≪≫ Sigma.mapIso j

private theorem sigmaNaturality
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ D) (H : A ⥤ B) (G : B ⥤ D)
    (t : ∀ M, F.obj M ⟶ G.obj (H.obj M))
    (ht : ∀ {M N} (v : M ⟶ N), F.map v ≫ t N = t M ≫ G.map (H.map v))
    {J : Type*} (U : J → A) [HasCoproduct U]
    [HasCoproduct (fun i ↦ F.obj (U i))] [HasCoproduct (fun i ↦ H.obj (U i))]
    [HasCoproduct (fun i ↦ G.obj (H.obj (U i)))]
    [HasCoproduct (fun i ↦ (H ⋙ G).obj (U i))]
    {M : A} (e : (∐ U) ⟶ M) :
    sigmaComparison F U ≫ F.map e ≫ t M =
      CategoryTheory.Limits.Sigma.map (fun i ↦ t (U i)) ≫
        sigmaComparison G (fun i ↦ H.obj (U i)) ≫
        G.map (sigmaComparison H U) ≫ (H ⋙ G).map e := by
  apply Sigma.hom_ext
  intro i
  simp only [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc,
    Functor.comp_obj, Functor.comp_map]
  rw [← G.map_comp_assoc, ι_comp_sigmaComparison]
  simpa only [Functor.map_comp, Category.assoc] using
    ht (Sigma.ι U i ≫ e)

private theorem isIsoDesc
    {A : Type*} [Category A] {I : Type*} [Category I]
    {D : I ⥤ A} [HasColimit D] (v : Cocone D) (hv : IsColimit v) :
    IsIso (colimit.desc D v) :=
  hv.coconePointUniqueUpToIso (colimit.isColimit D) |>.isIso_inv

private theorem isIsoDescOfPreserves
    {A B : Type*} [Category A] [Category B] {I : Type*} [Category I]
    (P : I ⥤ A) (v : Cocone P) (hv : IsColimit v) (F : A ⥤ B)
    [HasColimit (P ⋙ F)] [PreservesColimit P F] :
    IsIso (colimit.desc (P ⋙ F) (F.mapCocone v)) :=
  isIsoDesc _ (isColimitOfPreserves F hv)

private def transportColimit
    {A : Type*} [Category A] {I : Type*} [Category I]
    {D E : I ⥤ A} (v : Cocone D) (w : Cocone E) (eta : D ≅ E) (e : v.pt ≅ w.pt)
    (he : ∀ i, v.ι.app i ≫ e.hom = eta.hom.app i ≫ w.ι.app i)
    (hv : IsColimit v) : IsColimit w :=
  (IsColimit.precomposeHomEquiv eta w)
    (IsColimit.ofIsoColimit hv (Cocone.ext e he))

private theorem isIsoDescOfComparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    {I : Type*} [Category I] (P : I ⥤ A) (v : Cocone P)
    (F G : A ⥤ B) (H : B ⥤ D)
    [HasColimit (P ⋙ F ⋙ H)] [HasColimit (P ⋙ G ⋙ H)]
    (eta : P ⋙ F ≅ P ⋙ G) (e : F.obj v.pt ≅ G.obj v.pt)
    (he : ∀ i, F.map (v.ι.app i) ≫ e.hom = eta.hom.app i ≫ G.map (v.ι.app i))
    (hc : IsIso (colimit.desc (P ⋙ F ⋙ H) ((F ⋙ H).mapCocone v))) :
    IsIso (colimit.desc (P ⋙ G ⋙ H) ((G ⋙ H).mapCocone v)) := by
  have : IsIso ((colimit.isColimit (P ⋙ F ⋙ H)).desc ((F ⋙ H).mapCocone v)) := by
    change IsIso (colimit.desc _ _)
    exact hc
  have hv : IsColimit ((F ⋙ H).mapCocone v) := (colimit.isColimit _).ofPointIso
  exact isIsoDesc _ (transportColimit ((F ⋙ H).mapCocone v) ((G ⋙ H).mapCocone v)
    (Functor.isoWhiskerRight eta H) (H.mapIso e)
    (fun i ↦ by
      change H.map (F.map (v.ι.app i)) ≫ H.map e.hom =
        H.map (eta.hom.app i) ≫ H.map (G.map (v.ι.app i))
      simpa only [Functor.map_comp] using congrArg H.map (he i)) hv)

namespace AlgebraicGeometry.Scheme.FilteredFiniteFreeProjection

attribute [local irreducible] RingedDerivedNative.tensorIso

private def flatToKFlat (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ObjectProperty.ιOfLE (P := proEtaleFlatRepresentatives X R)
    (P' := CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R))
    (fun _ h ↦ h.1)

private def nativeModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : ProEtaleTensorModel X R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology X) R)
  representative := Functor.isoWhiskerLeft ((flatToKFlat X R).prod (flatToKFlat X R))
    (RingedDerivedNative.comparison.{u + 1, u, 0, u + 2} (ProEt.topology X) R)

@[irreducible] private def nativeTensorIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P L : CochainComplex (proEtaleRingModules X R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (R := R) L) :
    DerivedCategory.Q.obj ((WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
      (ProEt.topology X) R).obj (P, L)) ≅
      (nativeModel X R).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) :=
  RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2} (ProEt.topology X) R P L h

private theorem nativeTensorIso_naturality (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P L P' L' : CochainComplex (proEtaleRingModules X R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (R := R) L)
    (h' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P' ∨
      CochainComplex.IsKFlatIndependentCoefficients (R := R) L')
    (v : P ⟶ P') (w : L ⟶ L') :
    DerivedCategory.Q.map ((WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
      (ProEt.topology X) R).map (Prod.mkHom v w)) ≫
        (nativeTensorIso X R P' L' h').hom =
      (nativeTensorIso X R P L h).hom ≫ (nativeModel X R).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map v) (DerivedCategory.Q.map w)) := by
  unfold nativeTensorIso
  exact RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
    (ProEt.topology X) R P L P' L' h h' v w

private theorem resolvingFF (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (((Functor.whiskeringLeft
      ((proEtaleFlatRepresentatives X R).FullSubcategory ×
        (proEtaleFlatRepresentatives X R).FullSubcategory)
      (DerivedCategory (proEtaleRingModules X R) ×
        DerivedCategory (proEtaleRingModules X R))
      (DerivedCategory (proEtaleRingModules X R))).obj
      (((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let P := proEtaleFlatRepresentatives X R
  let H : ObjectProperty (HomotopyCategory (proEtaleRingModules X R) (.up ℤ)) :=
    fun T ↦ P T.as
  have hres : ∀ T, ∃ (K : H.FullSubcategory) (p : K.obj ⟶ T),
      (HomotopyCategory.quasiIso _ (.up ℤ)) p := by
    intro T
    obtain ⟨K, p, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) T.as
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := R) (K.X n) := fun n ↦
      (CategoryTheory.exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (K.X n)).symm (hf n)
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj K, hk, hflat⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (DerivedCategory (proEtaleRingModules X R))
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh P H
    (fun _ ↦ Iff.rfl) hres
  let e := Functor.isoWhiskerLeft P.ι
    (DerivedCategory.quotientCompQhIso (proEtaleRingModules X R))
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ _).mapIso (NatIso.prod e e))⟩

private theorem tensorModelIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a b : ProEtaleTensorModel X R) :
    Nonempty (a.tensor ≅ b.tensor) := by
  obtain ⟨ff⟩ := resolvingFF X R
  exact ⟨ff.preimageIso (a.representative.symm ≪≫ b.representative)⟩

private theorem fixedTensorAdditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a : ProEtaleTensorModel X R)
    (C : DerivedCategory (proEtaleRingModules X R)) :
    ((Functor.curryObj a.tensor).flip.obj C).Additive := by
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} (ProEt.topology X) R
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} (ProEt.topology X) R
  let := RingedDerivedNative.modulePreadditive.{u + 1, u, 0} (ProEt.topology X) R
  let := RingedDerivedNative.moduleClosed.{u + 1, u, 0} (ProEt.topology X) R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  let : HasColimitsOfSize.{0, 0} (proEtaleRingModules X R) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} (proEtaleRingModules X R)
  let := SheafOfModules.cochainTensorLeftPreservesColimits R
  let := SheafOfModules.cochainTensorRightPreservesColimits R
  let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology X) R
  have : IsGrothendieckAbelian.{u + 1} (proEtaleRingModules X R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology X) R).1
  have := DerivedCategory.additive_tensorRight (A := proEtaleRingModules X R) C
  obtain ⟨e⟩ := tensorModelIso X R (nativeModel X R) a
  exact fixedTensorAdditiveOfIso a.tensor C e

private theorem tensorUnitAction (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a : ProEtaleTensorModel X R) :
    Nonempty ((Functor.curryObj a.tensor).obj
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ≅ 𝟭 _) := by
  let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology X) R
  obtain ⟨e⟩ := tensorModelIso X R a (nativeModel X R)
  let := SheafOfModules.cochainModulesMonoidal R
  let un := (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
    (ProEt.topology X) R).symm
  exact ⟨(Functor.curry.mapIso e).app _ ≪≫ (curryTensorIso _).app _ ≪≫
    (MonoidalCategory.curriedTensor _).mapIso un ≪≫
      MonoidalCategory.leftUnitorNatIso _⟩

attribute [local irreducible] nativeModel RingedDerivedNative.monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flatTensorHomologyPreservesFilteredColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a : ProEtaleTensorModel X R)
    (D : DerivedCategory (proEtaleRingModules X R))
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] (q : ℤ) :
    PreservesColimitsOfShape I (DerivedCategory.singleFunctor _ 0 ⋙
      (Functor.curryObj a.tensor).flip.obj D ⋙ DerivedCategory.homologyFunctor _ q) := by
  let M := proEtaleRingModules X R
  let K₀ := (DerivedCategory.Q (C := M)).objPreimage D
  obtain ⟨K, p, hk, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K₀
  have : QuasiIso p := hq
  let e : DerivedCategory.Q.obj K ≅ D :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso D
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesPreadditive R
  let T := ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K
  let s := CochainComplex.singleFunctor M 0
  let H := DerivedCategory.homologyFunctor M q
  let n := nativeModel X R
  let r : s ⋙ T ⋙ DerivedCategory.Q ≅ DerivedCategory.singleFunctor M 0 ⋙
      (Functor.curryObj n.tensor).flip.obj (DerivedCategory.Q.obj K) :=
    NatIso.ofComponents (fun A ↦ nativeTensorIso X R (s.obj A) K (Or.inr hk)) (by
        intro A B v
        have hn := nativeTensorIso_naturality X R (s.obj A) K (s.obj B) K
          (Or.inr hk) (Or.inr hk) (s.map v) (𝟙 K)
        have hm : (WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
            (ProEt.topology X) R).map
              (X := (s.obj A, K)) (Y := (s.obj B, K))
              (Prod.mkHom (s.map v) (𝟙 K)) = T.map (s.map v) :=
          uncurryMapRightId ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
            (.up ℤ) (.up ℤ) (.up ℤ)) (s.map v) K
        rw [hm] at hn
        change DerivedCategory.Q.map (T.map (s.map v)) ≫ _ =
          _ ≫ n.tensor.map (Prod.mkHom (DerivedCategory.Q.map (s.map v))
            (𝟙 (DerivedCategory.Q.obj K)))
        simpa only [CategoryTheory.Functor.map_id] using hn)
  have hz : Nonempty (n.tensor ≅ a.tensor) := tensorModelIso X R n a
  let z := Classical.choice hz
  let rD := r ≪≫ Functor.isoWhiskerLeft (DerivedCategory.singleFunctor M 0)
    (fixedTensorIso n.tensor a.tensor z e)
  have (N : M) : PreservesColimitsOfShape I (MonoidalCategory.tensorRight N) :=
    by
      have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R N
      exact preservesColimitsOfShape_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight N)
  have : PreservesColimitsOfShape I T := by dsimp [T]; infer_instance
  have : PreservesColimitsOfShape I s := by
    change PreservesColimitsOfShape I (HomologicalComplex.single M (.up ℤ) 0)
    infer_instance
  have : IsGrothendieckAbelian.{u + 1} (proEtaleRingModules X R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology X) R).1
  have : HasExactColimitsOfShape I M := AB5OfSize.ofShape I
  have : PreservesColimitsOfShape I (s ⋙ T ⋙ HomologicalComplex.homologyFunctor M (.up ℤ) q) :=
    inferInstance
  let t := Functor.isoWhiskerLeft (s ⋙ T) (DerivedCategory.homologyFunctorFactors M q)
  have : PreservesColimitsOfShape I ((s ⋙ T ⋙ DerivedCategory.Q) ⋙ H) :=
    preservesColimitsOfShape_of_natIso t.symm
  exact preservesColimitsOfShape_of_natIso (Functor.isoWhiskerRight rD H)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (C : DerivedCategory (proEtaleRingModules X S))

/-- The coefficient-first source, using the recorded ordinary derived tensor.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection). -/
def source : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  DerivedCategory.singleFunctor _ 0 ⋙ (Functor.curryObj a.tensor).flip.obj
    ((proEtaleRingDerivedDirectImage f R S c).obj C)

/-- The tensor on X before applying derived direct image; LP is actual derived pullback.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection). -/
def tensorTarget : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules X S) :=
  DerivedCategory.singleFunctor _ 0 ⋙ proEtaleRingDerivedPullback f R S c ⋙
    (Functor.curryObj b.tensor).flip.obj C

/-- The target with its actual coefficient action and uncompleted derived direct image.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection). -/
def target : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  tensorTarget f R S c b C ⋙ proEtaleRingDerivedDirectImage f R S c

/-- The canonical counit mate, with the coefficient factor first.
Its defining adjunct is the canonical tensor comparison followed by 1 tensor counit.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection). -/
def projection (P : proEtaleRingModules Y R) :
    (source f R S c a C).obj P ⟶ (target f R S c b C).obj P :=
  (proEtaleRingDerivedAdjunction f R S c).homEquiv _ _
    ((proEtaleCanonicalTensorComparison f R S c a b).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj P,
        (proEtaleRingDerivedDirectImage f R S c).obj C) ≫
      b.tensor.map (Prod.mkHom (𝟙 _)
        ((proEtaleRingDerivedAdjunction f R S c).counit.app C)))

/-- Naturality includes the transitions and every specified colimit leg, without changing them.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection).
Proof: transpose both composites. Naturality of the canonical tensor comparison moves
Lu through that comparison; the remaining map is Lu tensor the same counit. The two
adjuncts agree, and injectivity of the adjunction bijection proves the equation. -/
theorem projection_naturality {P Q : proEtaleRingModules Y R} (v : P ⟶ Q) :
    (source f R S c a C).map v ≫ projection f R S c a b C Q =
      projection f R S c a b C P ≫ (target f R S c b C).map v := by
  exact tensorMateNaturality (proEtaleRingDerivedPullback f R S c)
    (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
    a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b).hom C
    ((DerivedCategory.singleFunctor _ 0).map v)

/-- The specified projection maps assembled into their natural transformation.
Source: Stacks 0B56 (blueprint: lem-sfb-filtered-finite-free-projection). -/
def projectionTransformation : source f R S c a C ⟶ target f R S c b C where
  app := projection f R S c a b C
  naturality _ _ v := projection_naturality f R S c a b C v

/-- The uniformly bounded strict diagram is single(LP) tensor K with the usual signed total.
Since LP occupies degree zero, its degree n is LP tensor K^n.
Source: Stacks 03EP, 06YU (blueprint: lem-sfb-filtered-finite-free-projection). -/
def strictTensor (K : CochainComplex (proEtaleRingModules X S) ℤ) :
    proEtaleRingModules Y R ⥤ CochainComplex (proEtaleRingModules X S) ℤ :=
  proEtaleRingModulePullback f R S c ⋙ CochainComplex.singleFunctor _ 0 ⋙
    ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj K

private theorem strictTensorBound
    (K : CochainComplex (proEtaleRingModules X S) ℤ) (n : ℤ)
    (hK : ∀ j : ℤ, j < n → IsZero (K.X j))
    (M : proEtaleRingModules Y R) (j : ℤ) (hj : j < n) :
    IsZero (((strictTensor f R S c K).obj M).X j) := by
  let e := CochainComplex.mapBifunctorSingle₁Iso (proEtaleOrdinaryTensor X S)
    ((proEtaleRingModulePullback f R S c).obj M) K
  exact (Functor.map_isZero ((proEtaleOrdinaryTensor X S).obj _)
    (hK j hj)).of_iso ((HomologicalComplex.eval _ _ j).mapIso e)

private theorem strictTensorPreservesColimits
    (K : CochainComplex (proEtaleRingModules X S) ℤ)
    (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I (strictTensor f R S c K) := by
  have (N : proEtaleRingModules X S) :
      PreservesColimitsOfShape I ((proEtaleOrdinaryTensor X S).flip.obj N) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients S N
    exact preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight N)
  have : PreservesColimitsOfShape I (proEtaleRingModulePullback f R S c) :=
    (proEtaleRingModuleAdjunction f R S c).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape I
      (CochainComplex.singleFunctor (proEtaleRingModules X S) 0) := by
    change PreservesColimitsOfShape I
      (HomologicalComplex.single (proEtaleRingModules X S) (.up ℤ) 0)
    infer_instance
  have : PreservesColimitsOfShape I
      (((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K) := by infer_instance
  unfold strictTensor
  infer_instance

private theorem freeFlat (Z : Scheme.{u})
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) (d : ℕ) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := T)
      (SheafOfModules.free
        (R := (sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)
        (ULift.{u + 1} (Fin d))) := by
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} (ProEt.topology Z) T
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} (ProEt.topology Z) T
  let := RingedDerivedNative.moduleClosed.{u + 1, u, 0} (ProEt.topology Z) T
  have : IsGrothendieckAbelian.{u + 1} (proEtaleRingModules Z T) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology Z) T).1
  have hu : ObjectProperty.flat (SheafOfModules.unit
      ((sheafCompose (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)) :=
    ObjectProperty.prop_unit ObjectProperty.flat
  have hf := ObjectProperty.flat_coproduct
    (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
      ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)) (fun _ ↦ hu)
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso T _).symm hf.2

private theorem pullbackUnit :
    Nonempty ((proEtaleRingDerivedPullback f R S c).obj
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))) := by
  let j := (proEtaleProjectionUnit_existsUnique f R S c).exists.choose
  exact ⟨(proEtaleRingDerivedPullbackFactors f R S c).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((proEtaleRingModulePullback f R S c).mapCochainComplexSingleFunctor 0).app _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso j⟩

private theorem flatOfIso (Z : Scheme.{u})
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    {M N : proEtaleRingModules Z T} (e : M ≅ N)
    (hN : SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := T) N) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := T) M := by
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    ((SheafOfModules.siteSheafTensorRightIso T N) ≪≫
      (proEtaleOrdinaryTensor Z T).flip.mapIso e.symm ≪≫
      (SheafOfModules.siteSheafTensorRightIso T M).symm) hN

private theorem pullbackFreeFlat (M : proEtaleRingModules Y R) (d : ℕ)
    (e : M ≅ SheafOfModules.free
      (R := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (ULift.{u + 1} (Fin d))) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj M) := by
  let L := proEtaleRingModulePullback f R S c
  have : L.IsLeftAdjoint := ⟨⟨_, ⟨proEtaleRingModuleAdjunction f R S c⟩⟩⟩
  let j := (proEtaleProjectionUnit_existsUnique f R S c).exists.choose
  let z := mapCoproductIso L
    (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) e (fun _ ↦ j)
  exact flatOfIso X S z (freeFlat X S d)

@[irreducible] private def pullbackSingleIso :
    DerivedCategory.singleFunctor _ 0 ⋙ proEtaleRingDerivedPullback f R S c ≅
      proEtaleRingModulePullback f R S c ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.isoWhiskerLeft (CochainComplex.singleFunctor _ 0)
      (proEtaleRingDerivedPullbackFactors f R S c) ≪≫
    Functor.isoWhiskerRight
      ((proEtaleRingModulePullback f R S c).mapCochainComplexSingleFunctor 0)
      DerivedCategory.Q

@[irreducible] private def strictTensorIso (K : CochainComplex (proEtaleRingModules X S) ℤ)
    (e : DerivedCategory.Q.obj K ≅ C) (M : proEtaleRingModules Y R)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj M))
    (z : (nativeModel X S).tensor ≅ b.tensor) :
    DerivedCategory.Q.obj ((strictTensor f R S c K).obj M) ≅
      (tensorTarget f R S c b C).obj M := by
  let hk := (SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
    S ((proEtaleRingModulePullback f R S c).obj M) hM).choose
  exact nativeTensorIso X S
      ((CochainComplex.singleFunctor _ 0).obj
        ((proEtaleRingModulePullback f R S c).obj M)) K (Or.inl hk) ≪≫
    z.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((proEtaleRingModulePullback f R S c).obj M)), DerivedCategory.Q.obj K) ≪≫
    b.tensor.mapIso
      (Iso.prod ((pullbackSingleIso f R S c).app M).symm e)

private theorem strictTensorIso_naturality
    (K : CochainComplex (proEtaleRingModules X S) ℤ) (e : DerivedCategory.Q.obj K ≅ C)
    {M N : proEtaleRingModules Y R} (v : M ⟶ N)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj M))
    (hN : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj N))
    (z : (nativeModel X S).tensor ≅ b.tensor) :
    DerivedCategory.Q.map ((strictTensor f R S c K).map v) ≫
        (strictTensorIso f R S c b C K e N hN z).hom =
      (strictTensorIso f R S c b C K e M hM z).hom ≫
        (tensorTarget f R S c b C).map v := by
  let P := CochainComplex.singleFunctor (proEtaleRingModules X S) 0
  let L := proEtaleRingModulePullback f R S c
  let hkM := (SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
    S (L.obj M) hM).choose
  let hkN := (SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
    S (L.obj N) hN).choose
  have hn := nativeTensorIso_naturality X S (P.obj (L.obj M)) K (P.obj (L.obj N)) K
    (Or.inl hkM) (Or.inl hkN) (P.map (L.map v)) (𝟙 K)
  unfold strictTensorIso
  dsimp only [id, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  have hmap : (WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
      (ProEt.topology X) S).map
        (X := (P.obj (L.obj M), K)) (Y := (P.obj (L.obj N), K))
        (Prod.mkHom (P.map (L.map v)) (𝟙 K)) =
      (strictTensor f R S c K).map v :=
    uncurryMapRightId ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)) (P.map (L.map v)) K
  have hn' := (congrArg DerivedCategory.Q.map hmap)
  have hn'' := congrArg (fun t ↦ t ≫
    (nativeTensorIso X S (P.obj (L.obj N)) K (Or.inl hkN)).hom) hn'
  have hn := hn''.symm.trans hn
  apply tensorComparisonNaturality (nativeModel X S).tensor b.tensor z
    (nativeTensorIso X S (P.obj (L.obj M)) K (Or.inl hkM))
    (nativeTensorIso X S (P.obj (L.obj N)) K (Or.inl hkN))
    ((pullbackSingleIso f R S c).app M).symm
    ((pullbackSingleIso f R S c).app N).symm e
    (DerivedCategory.Q.map ((strictTensor f R S c K).map v))
    (DerivedCategory.Q.map (P.map (L.map v)))
    ((proEtaleRingDerivedPullback f R S c).map
      ((DerivedCategory.singleFunctor _ 0).map v))
  · simpa only [CategoryTheory.Functor.map_id] using hn
  · exact (pullbackSingleIso f R S c).inv.naturality v

private theorem unitNormalization :
    ∃ (eA : (source f R S c a C).obj (SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
          (proEtaleRingDerivedDirectImage f R S c).obj C)
      (eC : (tensorTarget f R S c b C).obj (SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅ C),
      projection f R S c a b C (SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≫
        (proEtaleRingDerivedDirectImage f R S c).map eC.hom = eA.hom := by
  let L := proEtaleRingDerivedPullback f R S c
  let G := proEtaleRingDerivedDirectImage f R S c
  let U := (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  let H := (Functor.curryObj a.tensor).obj U
  let K := (Functor.curryObj b.tensor).obj (L.obj U)
  obtain ⟨h⟩ := tensorUnitAction Y R a
  obtain ⟨j⟩ := pullbackUnit f R S c
  obtain ⟨k₀⟩ := tensorUnitAction X S b
  let k : K ≅ 𝟭 _ := (Functor.curryObj b.tensor).mapIso j ≪≫ k₀
  let beta := proEtaleCanonicalTensorComparison f R S c a b
  let mu : H ⋙ L ≅ L ⋙ K := NatIso.ofComponents
    (fun Z ↦ beta.app (U, Z)) (by
      intro Z Z' v
      have hn := beta.hom.naturality (Prod.mkHom (𝟙 U) v)
      simpa [H, K, Functor.curryObj, Functor.comp_map, Functor.prod_map,
        L.map_id] using hn)
  have hm := unitMateIsIso L G (proEtaleRingDerivedAdjunction f R S c) H K h k mu C
  change IsIso (projection f R S c a b C _) at hm
  refine ⟨asIso (projection f R S c a b C _) ≪≫ G.mapIso (k.app C), k.app C, ?_⟩
  rfl

private theorem sourceAdditive : (source f R S c a C).Additive := by
  have := fixedTensorAdditive Y R a
    ((proEtaleRingDerivedDirectImage f R S c).obj C)
  unfold source
  infer_instance

private theorem tensorTargetAdditive : (tensorTarget f R S c b C).Additive := by
  have := fixedTensorAdditive X S b C
  unfold tensorTarget
  infer_instance

/-- Finite-free normalization with the coefficient first. The comparisons are the
canonical finite coproduct (and hence biproduct) comparisons, determined by injections.
The rank-one map is the unit-normalized counit mate; the triangle identity identifies
it with the identity after the tensor-unit identifications. This formula works for
EVERY presentation e, rather than choosing or changing a basis.
Source: Stacks 0944 (blueprint: lem-sfb-filtered-finite-free-projection).
Proof: the rank-one assertion is the tensor-unit normalization and triangle identity.
For the displayed formula precompose with each coproduct injection and apply projection
naturality to the corresponding basis injection. The finite-coproduct universal property
proves the equality. Additivity makes the comparisons isomorphisms, including rank zero. -/
theorem finiteFreeNormalization (P : proEtaleRingModules Y R) (d : ℕ)
    (e : SheafOfModules.free
      (R := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (ULift.{u + 1} (Fin d)) ≅ P) :
    (∃ (eA : (source f R S c a C).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
          (proEtaleRingDerivedDirectImage f R S c).obj C)
        (eC : (tensorTarget f R S c b C).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅ C),
      projection f R S c a b C (SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≫
        (proEtaleRingDerivedDirectImage f R S c).map eC.hom = eA.hom) ∧
    IsIso (sigmaComparison (source f R S c a C)
      (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ∧
    IsIso (sigmaComparison (tensorTarget f R S c b C)
      (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ∧
    IsIso (projection f R S c a b C
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ∧
    sigmaComparison (source f R S c a C)
        (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≫
      (source f R S c a C).map e.hom ≫ projection f R S c a b C P =
    CategoryTheory.Limits.Sigma.map (fun _ : ULift.{u + 1} (Fin d) ↦ projection f R S c a b C
        (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ≫
      sigmaComparison (proEtaleRingDerivedDirectImage f R S c)
        (fun _ : ULift.{u + 1} (Fin d) ↦ (tensorTarget f R S c b C).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ≫
      (proEtaleRingDerivedDirectImage f R S c).map
        (sigmaComparison (tensorTarget f R S c b C)
          (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
            ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) ≫
      (target f R S c b C).map e.hom := by
  classical
  obtain ⟨eA, eC, he⟩ := unitNormalization f R S c a b C
  have hu : IsIso (projection f R S c a b C (SheafOfModules.unit
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) := by
    have hcomp : IsIso (projection f R S c a b C (SheafOfModules.unit
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≫
        (proEtaleRingDerivedDirectImage f R S c).map eC.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((proEtaleRingDerivedDirectImage f R S c).map eC.hom)
  have := sourceAdditive f R S c a C
  have := tensorTargetAdditive f R S c b C
  refine ⟨⟨eA, eC, he⟩, inferInstance, inferInstance, hu, ?_⟩
  exact sigmaNaturality (source f R S c a C) (tensorTarget f R S c b C)
    (proEtaleRingDerivedDirectImage f R S c) (projection f R S c a b C)
    (fun v ↦ projection_naturality f R S c a b C v)
    (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (M := P) e.hom


private theorem finiteFreeIso (M : proEtaleRingModules Y R) (d : ℕ)
    (e : M ≅ SheafOfModules.free
      (R := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (ULift.{u + 1} (Fin d))) : IsIso (projection f R S c a b C M) := by
  change M ≅ (∐ fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) at e
  obtain ⟨_, hs, ht, hu, he⟩ := finiteFreeNormalization f R S c a b C M d e.symm
  simp only [Iso.symm_hom] at he
  have := sourceAdditive f R S c a C
  have := tensorTargetAdditive f R S c b C
  have (i : ULift.{u + 1} (Fin d)) : IsIso (projection f R S c a b C
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) := hu
  have : IsIso (sigmaComparison (source f R S c a C)
      (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≫
      (source f R S c a C).map e.inv ≫ projection f R S c a b C M) := by
    rw [he]
    infer_instance
  have : IsIso ((source f R S c a C).map e.inv ≫ projection f R S c a b C M) :=
    IsIso.of_isIso_comp_left
      (sigmaComparison (source f R S c a C)
        (fun _ : ULift.{u + 1} (Fin d) ↦ SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) _
  exact IsIso.of_isIso_comp_left ((source f R S c a C).map e.inv) _

attribute [local irreducible] Functor.rightDerivedFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual projection is invertible for a filtered finite-free colimit.
Source: Hemo--Richarz--Scholbach 5.3(1), (5.4), and Stacks 0944
(blueprint: lem-sfb-filtered-finite-free-projection).
Proof: (1) normalized counit mates are natural and the ring coefficient gives the identity.
(2) Evaluate on the basis injections of each finite free P_i. The map is the finite
biproduct comparison, hence invertible, including rank zero. (3) Flat coefficients
compute derived tensor termwise, naturally in the coefficient, by a single K-flat
resolution. (4) Tensor commutes with filtered colimits, which are exact, so homology
of the source tensor is the colimit of the source homologies. (5) Pullback preserves
the coefficient colimit. Choose a representative K of C zero below a; all LP_i tensor K
and LB tensor K have that same lower bound. (6) Apply bounded-below qcqs direct-image
continuity, restricting the f_*S action along R to obtain the stated R-linear map.
(7) The cocone equation identifies H^q(delta_B) with the colimit of the finite-free
maps followed by continuity, using the actual legs. (8) Direct image preserves D^+
by bounded-below injective representatives. Flat tensor preserves the lower bounds,
so cohomological detection proves that delta_B is an isomorphism in the derived category. -/
theorem filteredFiniteFreeProjection [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ proEtaleRingModules Y R) (v : Cocone P) (hv : IsColimit v)
    (hP : ∀ i : I, ∃ d : ℕ, Nonempty (P.obj i ≅ SheafOfModules.free
      (R := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ULift.{u + 1} (Fin d))))
    (hB : SheafOfModules.IsFlatOnSite (J := ProEt.topology Y) (R := R) v.pt)
    (hLB : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj v.pt))
    (hC : ∃ n : ℤ, C.IsGE n) :
    IsIso (projection f R S c a b C v.pt) ∧
      (∀ i : I, IsIso (projection f R S c a b C (P.obj i))) ∧
      ∀ q : ℤ,
        IsIso (colimit.desc (P ⋙ source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
          ((source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v)) ∧
        IsIso (colimit.desc (P ⋙ target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q)
          ((target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v)) ∧
        colimit.desc (P ⋙ source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
            ((source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v) ≫
          (DerivedCategory.homologyFunctor _ q).map (projection f R S c a b C v.pt) =
        colimMap (Functor.whiskerLeft P
            (Functor.whiskerRight (projectionTransformation f R S c a b C)
              (DerivedCategory.homologyFunctor _ q))) ≫
          colimit.desc (P ⋙ target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q)
            ((target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v) ∧
        ∀ (K : CochainComplex (proEtaleRingModules X S) ℤ) (n : ℤ),
          (∀ j : ℤ, j < n → IsZero (K.X j)) →
          (DerivedCategory.Q.obj K ≅ C) →
          ∃ (eta : P ⋙ strictTensor f R S c K ⋙ DerivedCategory.Q ≅
              P ⋙ tensorTarget f R S c b C)
            (eB : DerivedCategory.Q.obj ((strictTensor f R S c K).obj v.pt) ≅
              (tensorTarget f R S c b C).obj v.pt),
            (∀ (i : I) (j : ℤ), j < n →
              IsZero (((strictTensor f R S c K).obj (P.obj i)).X j)) ∧
            (∀ j : ℤ, j < n →
              IsZero (((strictTensor f R S c K).obj v.pt).X j)) ∧
            (∀ i : I, DerivedCategory.Q.map ((strictTensor f R S c K).map (v.ι.app i)) ≫
                eB.hom = eta.hom.app i ≫ (tensorTarget f R S c b C).map (v.ι.app i)) ∧
            Nonempty (IsColimit ((strictTensor f R S c K).mapCocone v)) ∧
            IsIso (colimit.desc
              (P ⋙ strictTensor f R S c K ⋙ DerivedCategory.Q ⋙
                proEtaleRingDerivedDirectImage f R S c ⋙ DerivedCategory.homologyFunctor _ q)
              ((strictTensor f R S c K ⋙ DerivedCategory.Q ⋙
                proEtaleRingDerivedDirectImage f R S c ⋙
                DerivedCategory.homologyFunctor _ q).mapCocone v)) := by
  classical
  have _ := hB
  let z := Classical.choice (tensorModelIso X S (nativeModel X S) b)
  have hPi (i : I) : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj (P.obj i)) := by
    obtain ⟨d, ⟨e⟩⟩ := hP i
    exact pullbackFreeFlat f R S c (P.obj i) d e
  have hi (i : I) : IsIso (projection f R S c a b C (P.obj i)) := by
    obtain ⟨d, ⟨e⟩⟩ := hP i
    exact finiteFreeIso f R S c a b C (P.obj i) d e
  have hs (q : ℤ) : IsIso (colimit.desc
      (P ⋙ source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
      ((source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v)) := by
    have : PreservesColimitsOfShape I
        (source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q) :=
      flatTensorHomologyPreservesFilteredColimits Y R a
        ((proEtaleRingDerivedDirectImage f R S c).obj C) I q
    exact isIsoDescOfPreserves P v hv
      (source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
  have hd (q : ℤ) (K : CochainComplex (proEtaleRingModules X S) ℤ) (n : ℤ)
      (hK : ∀ j : ℤ, j < n → IsZero (K.X j)) (e : DerivedCategory.Q.obj K ≅ C) :
          ∃ (eta : P ⋙ strictTensor f R S c K ⋙ DerivedCategory.Q ≅
              P ⋙ tensorTarget f R S c b C)
            (eB : DerivedCategory.Q.obj ((strictTensor f R S c K).obj v.pt) ≅
              (tensorTarget f R S c b C).obj v.pt),
            (∀ (i : I) (j : ℤ), j < n →
              IsZero (((strictTensor f R S c K).obj (P.obj i)).X j)) ∧
            (∀ j : ℤ, j < n →
              IsZero (((strictTensor f R S c K).obj v.pt).X j)) ∧
            (∀ i : I, DerivedCategory.Q.map ((strictTensor f R S c K).map (v.ι.app i)) ≫
                eB.hom = eta.hom.app i ≫ (tensorTarget f R S c b C).map (v.ι.app i)) ∧
            Nonempty (IsColimit ((strictTensor f R S c K).mapCocone v)) ∧
            IsIso (colimit.desc
              (P ⋙ strictTensor f R S c K ⋙ DerivedCategory.Q ⋙
                proEtaleRingDerivedDirectImage f R S c ⋙ DerivedCategory.homologyFunctor _ q)
              ((strictTensor f R S c K ⋙ DerivedCategory.Q ⋙
                proEtaleRingDerivedDirectImage f R S c ⋙
                DerivedCategory.homologyFunctor _ q).mapCocone v)) := by
    let eta : P ⋙ strictTensor f R S c K ⋙ DerivedCategory.Q ≅
        P ⋙ tensorTarget f R S c b C := NatIso.ofComponents
      (fun i ↦ strictTensorIso f R S c b C K e (P.obj i) (hPi i) z)
      (fun v ↦ strictTensorIso_naturality f R S c b C K e (P.map v) _ _ z)
    let eB := strictTensorIso f R S c b C K e v.pt hLB z
    have hleg (i : I) : DerivedCategory.Q.map
        ((strictTensor f R S c K).map (v.ι.app i)) ≫ eB.hom =
        eta.hom.app i ≫ (tensorTarget f R S c b C).map (v.ι.app i) :=
      strictTensorIso_naturality f R S c b C K e (v.ι.app i) (hPi i) hLB z
    have := strictTensorPreservesColimits f R S c K I
    have hc := isColimitOfPreserves (strictTensor f R S c K) hv
    have hb (i : I) (j : ℤ) (hj : j < n) := strictTensorBound f R S c K n hK (P.obj i) j hj
    have hcont := ProEt.boundedContinuityDirectImage_coefficients f R S c
      (P ⋙ strictTensor f R S c K) ((strictTensor f R S c K).mapCocone v) hc n hb q
    exact ⟨eta, eB, hb, strictTensorBound f R S c K n hK v.pt, hleg, ⟨hc⟩, hcont⟩
  have ht (q : ℤ) : IsIso (colimit.desc
      (P ⋙ target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q)
      ((target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q).mapCocone v)) := by
    obtain ⟨n, hn⟩ := hC
    have := hn
    obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE C n
    obtain ⟨eta, eB, _, _, hleg, _, hcont⟩ := hd q K n
      (fun j hj ↦ K.isZero_of_isStrictlyGE n j hj) e.symm
    let H := proEtaleRingDerivedDirectImage f R S c ⋙ DerivedCategory.homologyFunctor _ q
    exact isIsoDescOfComparison P v
      (strictTensor f R S c K ⋙ DerivedCategory.Q) (tensorTarget f R S c b C)
      H eta eB hleg hcont
  have he (q : ℤ) := colimitDescNaturality P v
    (source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
    (target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q)
    (Functor.whiskerRight (projectionTransformation f R S c a b C)
      (DerivedCategory.homologyFunctor _ q))
  have hBiso : IsIso (projection f R S c a b C v.pt) := by
    apply (DerivedCategory.isIso_iff _ (projection f R S c a b C v.pt)).2
    intro q
    have := hs q
    have := ht q
    have (i : I) : IsIso ((DerivedCategory.homologyFunctor _ q).map
        (projection f R S c a b C (P.obj i))) := inferInstance
    exact isIsoAppOfColimitDesc P v
      (source f R S c a C ⋙ DerivedCategory.homologyFunctor _ q)
      (target f R S c b C ⋙ DerivedCategory.homologyFunctor _ q)
      (Functor.whiskerRight (projectionTransformation f R S c a b C)
        (DerivedCategory.homologyFunctor _ q))
      (fun i ↦ inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ q).map
        (projection f R S c a b C (P.obj i)))))
  exact ⟨hBiso, hi, fun q ↦ ⟨hs q, ht q, he q, hd q⟩⟩

end AlgebraicGeometry.Scheme.FilteredFiniteFreeProjection
