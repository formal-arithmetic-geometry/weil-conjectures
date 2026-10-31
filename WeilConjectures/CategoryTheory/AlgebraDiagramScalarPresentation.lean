/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.ExtensionTensorComparisonIndependent
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization

/-! # Normalized derived scalar presentation

Source: Stacks 03CY, 06YU and 07A4.
(blueprint: lem-pur-algebra-diagram-scalar-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
set_option synthInstance.maxSize 4096

universe u w v v' v'' u' u''
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open scoped ZeroObject ChangeOfRings
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}

variable {B : Sheaf K CommRingCat.{u}} (a : R ⟶ B)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)]
  [ExactRestriction a]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def ordinaryIso
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a) :
    m.E ≅ extensionFunctor.{u, u, u} a :=
  NatIso.ofComponents (fun M ↦ eqToIso (m.obj_eq M)) (by
    intro M N f
    rw [m.map_eq]
    simp [extensionFunctor, Category.assoc])

open MonoidalCategory
open SheafOfModules.KFlatFixedTensor hiding Modules
open SheafOfModules.PullbackTensorCanonical
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] DerivedCategory.Q
attribute [local irreducible] canonicalDerivedTensor canonicalRepresentativeIso
attribute [local irreducible] Functor.curry
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local semireducible] canonicalDerivedTensor canonicalRepresentativeIso
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def ordinaryTotal (t : ScalarTensorPresentation a)
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a) :
    (((curriedTensor (Modules.{u, u, u} R)).flip.obj (coefficient a)).mapHomologicalComplex
      (.up ℤ)) ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex.{u, u, u, u} a :=
  NatIso.mapHomologicalComplex
      (t.iso ≪≫ Functor.isoWhiskerRight (ordinaryIso a m).symm
        (restrictionFunctor.{u, u, u, u} a)) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      (m.E ⋙ restrictionFunctor.{u, u, u, u} a)) (.up ℤ)).symm

private def fixedSecond {A : Type u} [Category.{v} A] (Y : A) : A ⥤ A × A where
  obj X := (X, Y)
  map f := (f, 𝟙 Y)

private theorem unary_descent
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {E : Type u''} [Category.{v''} E] (q : A ⥤ B) (X₀ : A)
    (ff : ((Functor.whiskeringLeft (A × A) (B × B) E).obj (q.prod q)).FullyFaithful)
    {F G : B ⥤ E} (e : q ⋙ F ≅ q ⋙ G) :
    ∃ t : F ≅ G, ∀ X, t.app (q.obj X) = e.app X := by
  let fstA : A × A ⥤ A := Prod.fst _ _
  let fstB : B × B ⥤ B := Prod.fst _ _
  let ee : (q.prod q) ⋙ (fstB ⋙ F) ≅ (q.prod q) ⋙ (fstB ⋙ G) :=
    Functor.isoWhiskerLeft fstA e
  let tt : fstB ⋙ F ≅ fstB ⋙ G := ff.preimageIso ee
  let t : F ≅ G := Functor.isoWhiskerLeft (fixedSecond (q.obj X₀)) tt
  refine ⟨t, ?_⟩
  intro X
  apply Iso.ext
  exact NatTrans.congr_app (ff.map_preimage ee.hom) (X, X₀)

omit [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)] in
private theorem extension_map_tmul (a : R ⟶ B) {M N : Modules.{u, u, u} R} (f : M ⟶ N)
    (V : Cᵒᵖ) (b : B.obj.obj V) (m : M.val.obj V) :
    ((extensionFunctor.{u, u, u} a).map f).val.app V (extensionTmul.{u, u, u} a M V b m) =
      extensionTmul.{u, u, u} a N V b (f.val.app V m) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).obj)
  let h : SheafOfModules.changeOfRingsPresheaf.{u, u, u} a M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} a N :=
    { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality a M f }
  have hn := congrArg (fun k ↦ k.app V (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] m))
    (adj.unit.naturality h)
  exact hn.symm

omit [HasDerivedCategory.{w} (Modules.{u, u, u} R)] in
private theorem tensor_ext (M N H : Modules.{u, u, u} R) {f g : M ⊗ N ⟶ H}
    (h : ∀ V (m : M.val.obj V) (n : N.val.obj V),
      f.val.app V (moduleTmul M N V m n) = g.val.app V (moduleTmul M N V m n)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv
      (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h V

omit [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)] in
private theorem scalar_tensor (a : R ⟶ B) : Nonempty (ScalarTensorPresentation a) := by
  choose e he using
    SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison.{u, u, u} a
  let t (M : Modules.{u, u, u} R) : M ⊗ coefficient.{u} a ≅
      (restrictionFunctor.{u, u, u, u} a).obj ((extensionFunctor.{u, u, u} a).obj M) :=
    (β_ M (coefficient.{u} a)) ≪≫ e M
  have ht (M : Modules.{u, u, u} R) (V : Cᵒᵖ) (m : M.val.obj V) (b : B.obj.obj V) :
      (t M).hom.val.app V (moduleTmul M (coefficient.{u} a) V m b) =
        extensionTmul.{u, u, u} a M V b m := by
    change (e M).hom.val.app V
      ((β_ M (coefficient.{u} a)).hom.val.app V (moduleTmul M (coefficient.{u} a) V m b)) = _
    exact (congrArg ((e M).hom.val.app V)
      (moduleTmul_braiding.{u, u, u} M (coefficient a) V m b)).trans (he M V b m)
  refine ⟨{ iso := NatIso.ofComponents t ?_, pure := ht }⟩
  intro M N f
  apply tensor_ext
  intro V m b
  change (t N).hom.val.app V ((f ▷ coefficient.{u} a).val.app V
      (moduleTmul M (coefficient.{u} a) V m b)) =
    ((extensionFunctor.{u, u, u} a).map f).val.app V ((t M).hom.val.app V
      (moduleTmul M (coefficient.{u} a) V m b))
  have hm := moduleTmul_map f (𝟙 (coefficient.{u} a)) V m b
  simp only [tensorHom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at hm
  rw [hm, ht, ht, extension_map_tmul]

private theorem scalar_tensor_derived (t : ScalarTensorPresentation a)
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a) :
    ∃ e : m.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory ≅
      scalarTensorFunctor.{u, w} a,
      IsNormalizedScalarTensor a m (ordinaryIso a m) t e := by
  obtain ⟨c, ⟨hn, hc⟩, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  let PR := SheafOfModules.PullbackTensorCanonical.resolvingProperty (R := R)
  let ε : PR.ι ⋙ ((DerivedCategory.Q ⋙ m.T) ⋙
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory) ⟶
      PR.ι ⋙ ((m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory) :=
    Functor.whiskerLeft PR.ι
      (Functor.whiskerRight m.ε ((restrictionFunctor.{u, u, u, u} a).mapDerivedCategory))
  have he (P : PR.FullSubcategory) : IsIso (ε.app P) := by
    have := m.computes P.obj P.property.1
    dsimp [ε]
    infer_instance
  let e₁ : PR.ι ⋙ DerivedCategory.Q ⋙ m.T ⋙
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory ≅
      PR.ι ⋙ m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
        (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (ε.app P) (he P))
      (fun f ↦ ε.naturality f)
  let e₂ : PR.ι ⋙ DerivedCategory.Q ⋙ scalarTensorFunctor.{u, w} a ≅
      PR.ι ⋙ (((curriedTensor (Modules.{u, u, u} R)).flip.obj
        (coefficient a)).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      unfold scalarTensorFunctor canonicalDerivedTensor
      exact c P.obj P.property.1 (coefficient a)) (by
      intro P P' f
      have h := hn P.obj P'.obj P.property.1 P'.property.1
        (coefficient a) (coefficient a) f.hom (𝟙 _)
      unfold scalarTensorFunctor canonicalDerivedTensor
      change ((derivedTensor R).map (DerivedCategory.Q.map f.hom)).app _ ≫ _ = _
      simpa only [Functor.map_id, NatTrans.mapHomologicalComplex_id,
        NatTrans.id_app, Category.comp_id, Category.id_comp, coefficientComplex,
        ordinaryTensor, Functor.comp_map, id_eq, ObjectProperty.ι_map] using h)
  let e : PR.ι ⋙
      (DerivedCategory.Q ⋙ m.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory) ≅
      PR.ι ⋙ DerivedCategory.Q ⋙ scalarTensorFunctor.{u, w} a :=
    e₁ ≪≫ Functor.isoWhiskerLeft (PR.ι ⋙ m.E.mapHomologicalComplex (.up ℤ))
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft PR.ι (Functor.isoWhiskerRight (ordinaryTotal a t m).symm
        DerivedCategory.Q) ≪≫ e₂.symm
  obtain ⟨ff⟩ := SheafOfModules.PullbackTensorCanonical.resolving_fullyFaithful
    (R := R) (S := R)
  obtain ⟨P₀, p₀, hp₀, hq₀⟩ :=
    SheafOfModules.PullbackTensorCanonical.exists_resolving (R := R)
      (0 : CochainComplex (Modules.{u, u, u} R) ℤ)
  obtain ⟨z, hz⟩ := unary_descent (PR.ι ⋙ DerivedCategory.Q) ⟨P₀, hp₀⟩ ff
    (Functor.associator PR.ι DerivedCategory.Q
        (m.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory) ≪≫ e ≪≫
      (Functor.associator PR.ι DerivedCategory.Q (scalarTensorFunctor.{u, w} a)).symm)
  refine ⟨z, ?_⟩
  intro P Q hp hq hf hg q hqiso
  have hzP := congrArg Iso.inv (hz ⟨P, hp, hf⟩)
  simp only [NatIso.trans_app, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Iso.app_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp] at hzP
  change z.inv.app (DerivedCategory.Q.obj P) = _ at hzP
  rw [hzP]
  simp only [e, NatIso.trans_app, Iso.trans_inv, Iso.app_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, e₁, e₂, NatIso.ofComponents_inv_app,
    NatIso.ofComponents_hom_app, asIso_inv, Iso.symm_inv, Category.assoc]
  simp only [ε, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc]
  unfold scalarTensorComparison
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  have hc' := hc P hp (coefficient a) P Q hp hq hf hg (𝟙 P) q
    (by infer_instance) hqiso
  simp only [Functor.map_id, NatTrans.id_app, Category.comp_id,
    Category.id_comp] at hc'
  simp only [Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, id_eq, ObjectProperty.ι_obj,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Functor.comp_obj, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  dsimp only [canonicalRepresentativeIso, canonicalDerivedTensor, scalarTensorFunctor]
  have hcomp := congrArg (fun z ↦ z ≫
    DerivedCategory.Q.map ((ordinaryTotal a t m).hom.app P) ≫
      DerivedCategory.Q.map ((restrictComplex a).map
        ((NatIso.mapHomologicalComplex (ordinaryIso a m) (.up ℤ)).hom.app P))) hc'
  calc
    _ = DerivedCategory.Q.map (((totalTensor R).obj P).map q ≫
        (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) (coefficient a) P).hom) ≫
        DerivedCategory.Q.map ((ordinaryTotal a t m).hom.app P) ≫
          DerivedCategory.Q.map ((restrictComplex a).map
            ((NatIso.mapHomologicalComplex (ordinaryIso a m) (.up ℤ)).hom.app P)) := by
      simpa only [Category.assoc] using hcomp
    _ = _ := by
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
      congr 1
      ext n : 1
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X,
        ordinaryTensor]
      dsimp only [ordinaryTotal, ScalarTensorPresentation.total,
        Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        Functor.mapHomologicalComplex, Iso.app, Iso.symm, Iso.trans,
        NatTrans.vcomp, NatTrans.id, NatTrans.mapHomologicalComplex]
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
        Iso.app_inv, NatTrans.comp_app, HomologicalComplex.comp_f,
        NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom, Iso.refl_inv,
        NatTrans.id_app, HomologicalComplex.id_f, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Category.id_comp, Category.assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
      erw [Category.comp_id]


private theorem normalized_adjunction
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a) :
    ∃ adj : m.T ⊣ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w},
      IsNormalizedScalarUnit a m (ordinaryIso a m) adj := by
  obtain ⟨a₀, adj, hn, ht⟩ :=
    SheafOfModules.ScalarPullback.normalized_adjunction_exists m
  have hu (M : Modules.{u, u, u} R) :
      a₀.unit.app M ≫ (restrictionFunctor.{u, u, u, u} a).map
          ((ordinaryIso a m).hom.app M) = (extensionAdjunction.{u, u, u} a).unit.app M := by
    ext U x
    have h := hn.1 M U x
    have he : ((extensionAdjunction.{u, u, u} a).unit.app M).val.app U x =
        extensionTmul.{u, u, u} a M U 1 x :=
      (Classical.choose_spec (extensionAdjunction_existsUnique.{u, u, u} a)).1 M U x
    change ((eqToHom (m.obj_eq M)).val.app U) ((a₀.unit.app M).val.app U x) = _
    apply Eq.trans (congrArg (fun z ↦ ((eqToHom (m.obj_eq M)).val.app U) z) h)
    apply Eq.trans _ he.symm
    change ((eqToHom (m.obj_eq M)).val.app U)
      (((eqToHom (m.obj_eq M).symm).val.app U)
        (extensionTmul.{u, u, u} a M U 1 x)) = extensionTmul.{u, u, u} a M U 1 x
    have hh := eqToHom_trans (m.obj_eq M).symm (m.obj_eq M)
    exact congrArg (fun f ↦ f.val.app U (extensionTmul.{u, u, u} a M U 1 x)) hh
  refine ⟨adj, ?_⟩
  intro P hp hf
  rw [← Category.assoc, ← Category.assoc]
  have ht' := ht P
  rw [Category.assoc (adj.unit.app (DerivedCategory.Q.obj P))]
  erw [ht']
  erw [← DerivedCategory.Q.map_comp]
  congr 1
  ext n : 1
  simp only [Adjunction.mapHomologicalComplex, scalarCochainUnit, restrictComplex,
    Functor.mapHomologicalComplexCompIso, Iso.app_inv, Iso.app_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatIso.mapHomologicalComplex_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplex_map_f, Iso.refl_inv, NatTrans.id_app,
    NatTrans.mapHomologicalComplex_app_f, Category.id_comp, Category.comp_id]
  dsimp only [Functor.mapHomologicalComplex, Iso.app, Iso.symm, Iso.trans,
    NatTrans.vcomp, NatTrans.id, NatTrans.mapHomologicalComplex,
    HomologicalComplex.Hom.isoOfComponents, NatIso.ofComponents]
  simp only [Category.id_comp, Category.comp_id]
  change a₀.unit.app (P.X n) ≫ (restrictionFunctor a).map
    ((ordinaryIso a m).hom.app (P.X n)) = (extensionAdjunction a).unit.app (P.X n)
  exact hu (P.X n)

/-- A normalized derived scalar presentation, with ordinary and two-resolving
factor tensor identifications. Construct the ordinary comparison on sheafified
pure tensors, descend on flat-term K-flat complexes, and use the normalized
coefficient adjunction for its unit. Source: Stacks 03CY, 06YU and 07A4
(blueprint: lem-pur-algebra-diagram-scalar-presentation). -/
theorem scalar_presentation : Nonempty (ScalarDerivedPresentation.{u, w} a) := by
  obtain ⟨m⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel a
  obtain ⟨t⟩ := scalar_tensor a
  obtain ⟨adj, hu⟩ := normalized_adjunction a m
  obtain ⟨e, he⟩ := scalar_tensor_derived a t m
  exact ⟨{
    model := m
    ordinary := ordinaryIso a m
    ordinary_hom := fun _ ↦ rfl
    adj := adj
    tensor := t
    underlyingIso := e
    unit_model := hu
    tensor_model := he }⟩
end CategoryTheory.AlgebraDiagramPullback
