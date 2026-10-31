/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.ConstructibleTensorRefinementWitness
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Tensor with a flat constructible etale sheaf

Source: Stacks Project, Etale Cohomology, Tags 095I and 0961, with the exact-functor
cohomology computation of Homology, Tag 010N
(blueprint: lem-fd-flat-constructible-tensor).

The two auxiliary bifunctors express naturality in both the bounded constructible complex
and the flat constructible sheaf. They use the existing small-etale module-sheaf tensor,
its unbounded derived tensor, and the recorded finite-value constructibility predicates.

## Main definitions

* `flatConstructibleEtaleSheafProperty`: the two hypotheses on the sheaf factor.
* `flatConstructibleTensorCohomologyLeft`: cohomology after derived tensor.
* `flatConstructibleTensorCohomologyRight`: ordinary tensor after cohomology.

## Main statements

* `flatConstructibleTensor_cohomology_and_bounds`: the natural comparison,
  constructibility, bounded constructibility, and preservation of every cohomology interval.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

section NativeCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc] private theorem nativeCollapse_ι (L : M) (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L E).hom.f i =
        (T.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

set_option backward.isDefEq.respectTransparency false in
private theorem nativeCollapse_naturality {L L' : M} (g : L ⟶ L')
    {E E' : CochainComplex M ℤ} (f : E ⟶ E') :
    HomologicalComplex.mapBifunctorMap f
        ((CochainComplex.singleFunctor _ 0).map g) T (.up ℤ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L' E').hom =
    (CochainComplex.mapBifunctorSingle₂Iso T L E).hom ≫
      ((T.flip.obj L).mapHomologicalComplex (.up ℤ)).map f ≫
        (NatTrans.mapHomologicalComplex (T.flip.map g) (.up ℤ)).app E' := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hq : q = 0
  · subst q
    have hp : p = i := by simpa using hpq
    subst p
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.ι_mapBifunctorMap_assoc]
    erw [nativeCollapse_ι, nativeCollapse_ι_assoc]
    have hg : ((CochainComplex.singleFunctor M 0).map g).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L').hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ≫ g := by
      change ((HomologicalComplex.single M (.up ℤ) 0).map g).f 0 ≫ _ = _
      simp [HomologicalComplex.single_map_f_self]
    simp [← Functor.map_comp, hg]
    rfl
  · apply IsZero.eq_of_src
    exact Functor.map_isZero (T.obj _)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end NativeCollapse

section NativeFlatTensor

universe v c

variable {C : Type c} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] in
private theorem nativeFlat (L : C) (hL : exactFunctor _ _ (tensorRight L)) :
    ObjectProperty.flat L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  exact ⟨⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm,
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm⟩, hL⟩

private theorem nativeTensorMuIso (L : C) (hL : exactFunctor _ _ (tensorRight L))
    (K : CochainComplex C ℤ) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K
      ((CochainComplex.singleFunctor C 0).obj L)) := by
  let P := (CochainComplex.singleFunctor C 0).obj L
  have hP := (CochainComplex.kFlat_single_obj_iff_flat L 0).2 (nativeFlat L hL)
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have hh := DerivedCategory.isIso_tensorRightCounit
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) hP'
  have hm : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
    exact inferInstanceAs (IsIso ((DerivedCategory.tensorRightCounit _).app _))
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
      DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K P)) ≫ _)
  infer_instance


private noncomputable def nativeQTensorIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) :
    DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ≅
      tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙ DerivedCategory.Q := by
  let a : DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⟶
      tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙ DerivedCategory.Q :=
    { app K := Functor.LaxMonoidal.μ DerivedCategory.Q K _
      naturality K K' f := Functor.LaxMonoidal.μ_natural_left _ f _ }
  have : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact nativeTensorMuIso L hL
  exact asIso a

private noncomputable def nativeCohomologyComparison (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (K : CochainComplex C ℤ) (i : ℤ) :
    (K ⊗ (CochainComplex.singleFunctor C 0).obj L).homology i ≅ K.homology i ⊗ L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  exact HomologicalComplex.homologyMapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) L K) i ≪≫
    (K.sc i).mapHomologyIso (tensorRight L)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nativeCohomologyNatIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) i ⋙ tensorRight L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  refine NatIso.ofComponents (fun K ↦ nativeCohomologyComparison L hL K i) ?_
  intro K K' f
  dsimp only [nativeCohomologyComparison, Iso.trans_hom,
    HomologicalComplex.homologyMapIso]
  change HomologicalComplex.homologyMap (f ▷ _) i ≫ _ = _
  have hn := congrArg (fun t ↦ HomologicalComplex.homologyMap t i)
    (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality (curriedTensor C) L f)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  change HomologicalComplex.homologyMap (f ▷ _) i ≫ _ = _ at hn
  erw [← Category.assoc, hn, Category.assoc]
  have hf := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map f) (tensorRight L)
  change HomologicalComplex.homologyMap
      (((tensorRight L).mapHomologicalComplex (.up ℤ)).map f) i ≫
      ((K'.sc i).mapHomologyIso (tensorRight L)).hom =
    ((K.sc i).mapHomologyIso (tensorRight L)).hom ≫
      (HomologicalComplex.homologyMap f i ▷ L) at hf
  erw [hf]
  simp only [Category.assoc]
  rfl


private noncomputable def nativeRestrictedIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    DerivedCategory.Q ⋙ (tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⋙
        DerivedCategory.homologyFunctor C i) ≅
      DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C i ⋙ tensorRight L) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (nativeQTensorIso L hL)
      (DerivedCategory.homologyFunctor C i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C i) ≪≫
    nativeCohomologyNatIso L hL i ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C i).symm _ ≪≫
    Functor.associator _ _ _

private noncomputable def nativeDerivedCohomologyIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⋙
        DerivedCategory.homologyFunctor C i ≅
      DerivedCategory.homologyFunctor C i ⋙ tensorRight L :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ _ _ (nativeRestrictedIso L hL i)

set_option backward.isDefEq.respectTransparency false in
private theorem nativeDerivedCohomologyIso_comparison (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (K : CochainComplex C ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor C i).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q K
          ((CochainComplex.singleFunctor C 0).obj L)) ≫
      (DerivedCategory.homologyFunctorFactors C i).hom.app
        (K ⊗ (CochainComplex.singleFunctor C 0).obj L) ≫
      (nativeCohomologyComparison L hL K i).hom =
    (nativeDerivedCohomologyIso L hL i).hom.app (DerivedCategory.Q.obj K) ≫
      ((DerivedCategory.homologyFunctorFactors C i).hom.app K ▷ L) := by
  dsimp only [nativeDerivedCohomologyIso]
  erw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    Category.comp_id, Category.id_comp]
  dsimp only [nativeRestrictedIso, nativeQTensorIso, nativeCohomologyNatIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, asIso_hom]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  erw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight, Category.comp_id]
  rfl

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
set_option backward.isDefEq.respectTransparency false in
private theorem nativeCohomologyComparison_right (L L' : C)
    (hL : exactFunctor _ _ (tensorRight L)) (hL' : exactFunctor _ _ (tensorRight L'))
    (g : L ⟶ L') (K : CochainComplex C ℤ) (i : ℤ) :
    HomologicalComplex.homologyMap
        (K ◁ (CochainComplex.singleFunctor C 0).map g) i ≫
      (nativeCohomologyComparison L' hL' K i).hom =
    (nativeCohomologyComparison L hL K i).hom ≫ (K.homology i ◁ g) := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  have := hL'.preservesFiniteLimits
  have := hL'.preservesFiniteColimits
  have hn := nativeCollapse_naturality (curriedTensor C) g (𝟙 K)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hh := congrArg (fun t ↦ HomologicalComplex.homologyMap t i) hn
  simp only [HomologicalComplex.homologyMap_comp] at hh
  dsimp only [nativeCohomologyComparison, Iso.trans_hom,
    HomologicalComplex.homologyMapIso]
  erw [← Category.assoc, hh]
  simp only [Category.assoc]
  have ht : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) (.up ℤ)).app K) i ≫
        ((K.sc i).mapHomologyIso (tensorRight L')).hom =
      ((K.sc i).mapHomologyIso (tensorRight L)).hom ≫ (K.homology i ◁ g) := by
    change ShortComplex.homologyMap ((K.sc i).mapNatTrans
      ((curriedTensor C).flip.map g)) ≫ _ = _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  erw [ht]

attribute [local irreducible] nativeDerivedCohomologyIso nativeRestrictedIso
  nativeCohomologyNatIso nativeCohomologyComparison

set_option backward.isDefEq.respectTransparency false in
private theorem nativeDerivedCohomologyIso_right (L L' : C)
    (hL : exactFunctor _ _ (tensorRight L)) (hL' : exactFunctor _ _ (tensorRight L'))
    (g : L ⟶ L') (i : ℤ) :
    Functor.whiskerRight
        ((curriedTensor (DerivedCategory C)).flip.map
          ((DerivedCategory.singleFunctor C 0).map g))
        (DerivedCategory.homologyFunctor C i) ≫
      (nativeDerivedCohomologyIso L' hL' i).hom =
    (nativeDerivedCohomologyIso L hL i).hom ≫
      Functor.whiskerLeft (DerivedCategory.homologyFunctor C i)
        ((curriedTensor C).flip.map g) := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro E
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let H := DerivedCategory.homologyFunctor C i
  let h := DerivedCategory.homologyFunctorFactors C i
  let σ := (curriedTensor (DerivedCategory C)).flip.map
    ((DerivedCategory.singleFunctor C 0).map g)
  let τ := (curriedTensor C).flip.map g
  apply (cancel_mono (h.hom.app E ▷ L')).1
  have hn : (nativeQTensorIso L hL).hom.app E ≫
      DerivedCategory.Q.map (E ◁ (CochainComplex.singleFunctor C 0).map g) =
    σ.app (DerivedCategory.Q.obj E) ≫ (nativeQTensorIso L' hL').hom.app E := by
    exact (Functor.LaxMonoidal.μ_natural_right DerivedCategory.Q E
      ((CochainComplex.singleFunctor C 0).map g)).symm
  have hc := nativeCohomologyComparison_right L L' hL hL' g E i
  have ht := τ.naturality (h.hom.app E)
  change (h.hom.app E ▷ L) ≫ (E.homology i ◁ g) =
    (H.obj (DerivedCategory.Q.obj E) ◁ g) ≫ (h.hom.app E ▷ L') at ht
  calc
    _ = H.map (σ.app (DerivedCategory.Q.obj E)) ≫
        (H.map ((nativeQTensorIso L' hL').hom.app E) ≫
          h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L') ≫
          (nativeCohomologyComparison L' hL' E i).hom) := by
      erw [Category.assoc, ← nativeDerivedCohomologyIso_comparison L' hL' E i]
      rfl
    _ = H.map ((nativeQTensorIso L hL).hom.app E) ≫
        H.map (DerivedCategory.Q.map (E ◁ (CochainComplex.singleFunctor C 0).map g)) ≫
        h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L') ≫
        (nativeCohomologyComparison L' hL' E i).hom := by
      erw [← H.map_comp_assoc, ← hn, H.map_comp, Category.assoc]
    _ = H.map ((nativeQTensorIso L hL).hom.app E) ≫
        h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L) ≫
        (nativeCohomologyComparison L hL E i).hom ≫ (E.homology i ◁ g) := by
      erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
      erw [hc]
      rfl
    _ = _ := by
      erw [reassoc_of% (nativeDerivedCohomologyIso_comparison L hL E i)]
      simp only [Category.assoc]
      erw [ht]
      rfl

private noncomputable def nativeComparison
    {D : Type*} [Category D] (P : ObjectProperty C)
    (hP : ∀ L, P L → exactFunctor _ _ (tensorRight L))
    (G : D ⥤ DerivedCategory C) (i : ℤ) :
    P.ι ⋙ DerivedCategory.singleFunctor C 0 ⋙ (curriedTensor (DerivedCategory C)).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj G ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.homologyFunctor C i) ≅
      P.ι ⋙ (curriedTensor C).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj (G ⋙ DerivedCategory.homologyFunctor C i) := by
  refine NatIso.ofComponents
    (fun L ↦ Functor.isoWhiskerLeft G
      (nativeDerivedCohomologyIso L.obj (hP L.obj L.property) i)) ?_
  intro L L' g
  apply NatTrans.ext
  funext K
  exact congr_app (nativeDerivedCohomologyIso_right L.obj L'.obj
    (hP L.obj L.property) (hP L'.obj L'.property) g.hom i) (G.obj K)

end NativeFlatTensor

attribute [local irreducible] nativeDerivedCohomologyIso nativeRestrictedIso
  nativeCohomologyNatIso nativeCohomologyComparison nativeQTensorIso nativeComparison

namespace AlgebraicGeometry.Etale

/-- The full-subcategory property bundling exactly the assumptions on `L`: constructibility
and exactness of `- ⊗ L`. The tensor is the existing sheafification of sectionwise tensor,
with its monoidal structure supplied explicitly, so no file-local instance is needed.
Source: Stacks, Tags 03ER(3) and 095I
(blueprint: lem-fd-flat-constructible-tensor). -/
def flatConstructibleEtaleSheafProperty
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun L ↦ Scheme.IsConstructibleEtaleModuleSheaf L ∧
    exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) L)

/-- The bifunctor `(L,K) ↦ Hⁱ(K ⊗ᴸ L[0])` on flat constructible sheaves and bounded
constructible complexes. Every map is supplied by composition of the existing functors.
Source: Stacks, Tags 06YU, 010N and 0961
(blueprint: lem-fd-flat-constructible-tensor). -/
noncomputable def flatConstructibleTensorCohomologyLeft
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) (i : ℤ) :
    (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory ⥤
      BoundedConstructibleDerivedCategory Λ X ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (flatConstructibleEtaleSheafProperty Λ X).ι ⋙
    _root_.DerivedCategory.singleFunctor _ 0 ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj (DerivedCategory.isBoundedConstructible Λ X).ι ⋙
    (Functor.whiskeringRight _ _ _).obj (_root_.DerivedCategory.homologyFunctor _ i)

/-- The bifunctor `(L,K) ↦ Hⁱ(K) ⊗ L`, with the ordinary tensor of module sheaves.
The full-subcategory inclusions retain all morphisms, so an isomorphism between these
bifunctors includes naturality in both variables, including arbitrary maps between flat
constructible sheaves.
Source: Stacks, Tags 095I and 010N
(blueprint: lem-fd-flat-constructible-tensor). -/
noncomputable def flatConstructibleTensorCohomologyRight
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) (i : ℤ) :
    (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory ⥤
      BoundedConstructibleDerivedCategory Λ X ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (flatConstructibleEtaleSheafProperty Λ X).ι ⋙
    (@curriedTensor _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj
      ((DerivedCategory.isBoundedConstructible Λ X).ι ⋙
        _root_.DerivedCategory.homologyFunctor _ i)

attribute [local irreducible] derivedTensor

private noncomputable def flatConstructibleComparison
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) (i : ℤ) :
    flatConstructibleTensorCohomologyLeft Λ X i ≅
      flatConstructibleTensorCohomologyRight Λ X i := by
  letI := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  unfold flatConstructibleTensorCohomologyLeft flatConstructibleTensorCohomologyRight
  unfold derivedTensor
  exact nativeComparison (flatConstructibleEtaleSheafProperty Λ X)
    (fun L hL ↦ hL.2) (DerivedCategory.isBoundedConstructible Λ X).ι i


private theorem constructibleTensor
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hA : Scheme.IsConstructibleEtaleModuleSheaf A)
    (hB : Scheme.IsConstructibleEtaleModuleSheaf B) :
    Scheme.IsConstructibleEtaleModuleSheaf
      (@tensorObj _ _
        (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).toMonoidalCategoryStruct
        A B) := by
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  obtain ⟨S, hS⟩ := hA
  obtain ⟨T, hT⟩ := hB
  let S' : Scheme.FiniteLocallyClosedStratification X :=
    { S with }
  let T' : Scheme.FiniteLocallyClosedStratification X :=
    { T with }
  exact (Scheme.constructible_tensor_refinement_witness A B S' T'
    S.isConstructible_stratum T.isConstructible_stratum
    (fun k ↦ (Scheme.finite_locally_constant_module_values_iff _).1.mp (hS k))
    (fun k ↦ (Scheme.finite_locally_constant_module_values_iff _).1.mp (hT k))).2.2.2.2

/-- Tensoring a bounded constructible complex with a flat constructible sheaf in degree
zero commutes naturally with cohomology. The cohomology sheaves are constructible, the
result is bounded constructible, and every interval containing the input cohomology also
contains the output cohomology. No finite Tor-amplitude assumption is made on the input.

Source: Stacks, Tags 095I and 0961, specialized to a flat degree-zero factor; Homology,
Tag 010N, and Cohomology on Sites, Tags 06YS and 06YU
(blueprint: lem-fd-flat-constructible-tensor).

Proof:
1. Exactness of `- ⊗ L` gives its cohomology comparison by
   `lem-weil-pbc-exact-functor-complex-cohomology`. The total tensor with `L[0]` has
   exactly one summand in each degree and differential `d ⊗ 1`, so it is that exact
   functor applied degreewise. In particular `L[0]` is K-flat
   (`def-pc-flat-sheaf-modules`, `def-kun-derived-tensor`, `def-pc-kflat-complex`).
2. Resolve an arbitrary representative of `K` by a flat-term K-flat complex using
   `lem-pc-kflat-resolution`. Its tensor with `L[0]` represents the derived tensor.
   Step 1 identifies its cohomology with `Hⁱ(K) ⊗ L`. The localization and tensor
   comparison of `lem-weil-pbc-site-derived-tensor-descent` make this natural in `K`.
   Maps of flat sheaves commute with tensor differentials, cycles and boundaries,
   making the same comparison natural in `L`.
3. Refine the constructible stratifications of `Hⁱ(K)` and `L` by their fibre products
   (`lem-weil-pbc-constructible-stratification-intersection`). Pullback preserves finite
   locally constant sheaves (`lemma-constructible-pullback-locally-constant`,
   `lemma-constructible-pullback-finite`), with the constant coefficient comparison of
   `prop-weil-pbc-inverse-image-modules-exact` retaining their module structures.
4. Ordinary pullback commutes with tensor
   (`lem-weil-pbc-ringed-topoi-module-pullback-tensor`). On each refined stratum the
   tensor is locally constant by `lem-weil-pbc-flc-tensor-locally-constant-part` and
   finite by `lem-weil-pbc-flc-tensor-finite-part`. Thus `Hⁱ(K) ⊗ L`, and hence step 2's
   cohomology sheaf, is constructible (`def-weil-pbc-etale-constructible-sheaf`).
5. Where `Hⁱ(K)` vanishes, step 2 identifies the output with `0 ⊗ L = 0`.
   Every interval is therefore preserved. Combined with step 4 this is bounded
   constructibility (`def-weil-pbc-constructible-complexes`). Only `L` was flat. -/
theorem flatConstructibleTensor_cohomology_and_bounds
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (∀ i : ℤ, Nonempty
      (flatConstructibleTensorCohomologyLeft Λ X i ≅
        flatConstructibleTensorCohomologyRight Λ X i)) ∧
    ∀ (L : (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory)
      (K : BoundedConstructibleDerivedCategory Λ X),
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K)) ∧
      DerivedCategory.isBoundedConstructible Λ X
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K.obj).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L.obj)) ∧
      ∀ a b : ℤ, a ≤ b →
        (∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj)) →
        ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K) := by
  classical
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e := flatConstructibleComparison Λ X
  refine ⟨fun i ↦ ⟨e i⟩, ?_⟩
  intro L K
  have hc (i : ℤ) : Scheme.IsConstructibleEtaleModuleSheaf
      (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K) := by
    have ht := constructibleTensor _ _ (K.property.1 i) L.property.1
    change Scheme.IsConstructibleEtaleModuleSheaf
      (((flatConstructibleTensorCohomologyRight Λ X i).obj L).obj K) at ht
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp ht
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso (((e i).app L).app K).symm)
  have hz (i : ℤ)
      (h : IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj)) :
      IsZero (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K) := by
    exact ((tensorRight L.obj).map_isZero h).of_iso (((e i).app L).app K)
  refine ⟨hc, ⟨hc, ?_⟩, fun a b _ h i hi ↦ hz i (h i hi)⟩
  obtain ⟨a, b, hab, h⟩ := K.property.2
  exact ⟨a, b, hab, fun i hi ↦ hz i (h i hi)⟩

end AlgebraicGeometry.Etale
