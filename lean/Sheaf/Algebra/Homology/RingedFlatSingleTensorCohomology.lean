/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Flat degree-zero tensor and unbounded cohomology on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 06YN, 06YS, 06YU and its preceding
localization construction; homology.tex, Tag 010N, exact functors on abelian categories.
(blueprint: lem-fd-ringed-flat-single-tensor-cohomology)

The derived-object comparison is included before its cohomology comparisons. All tensors
and representative comparisons are the published site-derived-tensor constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.FlatSingleTensor

variable {S : Type u} [Category.{v} S] [EssentiallySmall.{r} S]
  {J : GrothendieckTopology S} (R : Sheaf J CommRingCat.{r})

/-- The existing degree-zero complex functor, with no replacement of its data.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev degreeZero : Modules R ⥤ CochainComplex (Modules R) ℤ :=
  HomologicalComplex.single (Modules R) (.up ℤ) 0

/-- Ordinary signed direct-sum total tensor with the degree-zero right factor.
Source: Stacks, Tag 06YM (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev totalRight (L : Modules R) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (totalTensor R).flip.obj ((degreeZero R).obj L)

/-- Applying ordinary right tensor degree by degree.
Source: Stacks, Tag 010N (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev termwiseRight (L : Modules R) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (tensorRight L).mapHomologicalComplex (.up ℤ)

/-- The canonical degreewise identification: identity on the surviving (n,0) summand.
The imported construction uses the signed interchange, which is one in bidegree (n,0).
Source: Stacks, Tag 06YM (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev degreeComparison (L : Modules R) (K : CochainComplex (Modules R) ℤ) :
    (totalRight R L).obj K ≅ (termwiseRight R L).obj K :=
  CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules R)) L K

/-- The actual bifunctorial total-tensor map on a cochain map and a module map.
Source: Stacks, Tag 06YM (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev totalMap {K K' : CochainComplex (Modules R) ℤ} (f : K ⟶ K')
    {L L' : Modules R} (g : L ⟶ L') :
    (totalRight R L).obj K ⟶ (totalRight R L').obj K' :=
  HomologicalComplex.mapBifunctorMap f ((degreeZero R).map g) (curriedTensor _) (.up ℤ)

variable [HasDerivedCategory.{w} (Modules R)]

/-- The published K-flat derived tensor with the localized degree-zero right factor.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev derivedRight (L : Modules R) : DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) :=
  (derivedTensor R).flip.obj (DerivedCategory.Q.obj ((degreeZero R).obj L))

/-- The map of the published derived bifunctor on an arbitrary derived and module map.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev derivedMap {K K' : DerivedCategory (Modules R)} (f : K ⟶ K')
    {L L' : Modules R} (g : L ⟶ L') :
    (derivedRight R L).obj K ⟶ (derivedRight R L').obj K' :=
  (Functor.uncurry.obj (derivedTensor R)).map
    (X := (K, DerivedCategory.Q.obj ((degreeZero R).obj L)))
    (Y := (K', DerivedCategory.Q.obj ((degreeZero R).obj L')))
    (f, DerivedCategory.Q.map ((degreeZero R).map g))

set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedTensor
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso

private theorem derivedMap_right {K : DerivedCategory (Modules R)}
    {L L' : Modules R} (g : L ⟶ L') :
    derivedMap R (𝟙 K) g =
      ((derivedTensor R).flip.map (DerivedCategory.Q.map ((degreeZero R).map g))).app K := by
  change ((derivedTensor R).map (𝟙 K)).app _ ≫ _ = _
  rw [(derivedTensor R).map_id, NatTrans.id_app, Category.id_comp]
  rfl

private theorem derivedMap_left {K K' : DerivedCategory (Modules R)}
    (f : K ⟶ K') (L : Modules R) :
    derivedMap R f (𝟙 L) = (derivedRight R L).map f := by
  change ((derivedTensor R).map f).app _ ≫
    ((derivedTensor R).obj K').map (DerivedCategory.Q.map ((degreeZero R).map (𝟙 L))) = _
  rw [(degreeZero R).map_id, DerivedCategory.Q.map_id,
    ((derivedTensor R).obj K').map_id, Category.comp_id]
  rfl

omit [HasDerivedCategory (Modules R)] in
private theorem totalMap_right (K : CochainComplex (Modules R) ℤ)
    {L L' : Modules R} (g : L ⟶ L') :
    totalMap R (𝟙 K) g =
      ((totalTensor R).flip.map ((degreeZero R).map g)).app K := by
  simp [totalMap]

omit [HasDerivedCategory (Modules R)] in
private theorem totalMap_left {K K' : CochainComplex (Modules R) ℤ}
    (f : K ⟶ K') (L : Modules R) :
    totalMap R f (𝟙 L) = (totalRight R L).map f := by
  simp [totalMap]

section GenericCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc] private theorem collapse_ι (L : M) (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L E).hom.f i =
        (T.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

set_option backward.isDefEq.respectTransparency false in
private theorem collapse_naturality {L L' : M} (g : L ⟶ L')
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
    erw [collapse_ι, collapse_ι_assoc]
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

end GenericCollapse

omit [HasDerivedCategory (Modules R)] in
private theorem flat_exact (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    PreservesFiniteLimits (tensorRight L) ∧ PreservesFiniteColimits (tensorRight L) := by
  have h := hL
  change PreservesFiniteLimits (siteSheafTensorRight (A := R) L) ∧
    PreservesFiniteColimits (siteSheafTensorRight (A := R) L) at h
  have := h.1
  have := h.2
  exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R L),
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R L)⟩

private theorem single_properties (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    CochainComplex.IsKFlatIndependentCoefficients ((degreeZero R).obj L) ∧
      ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (((degreeZero R).obj L).X n) := by
  obtain ⟨hk, hf, _⟩ :=
    FlatSingleDerivedNormalization.flat_single_derived_normalization R L hL
  exact ⟨hk, hf⟩

private def cohomologyComparison (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (K : CochainComplex (Modules R) ℤ) (i : ℤ) :
    ((totalRight R L).obj K).homology i ≅ K.homology i ⊗ L := by
  have : PreservesFiniteLimits (tensorRight L) := (flat_exact R L hL).1
  have : PreservesFiniteColimits (tensorRight L) := (flat_exact R L hL).2
  exact HomologicalComplex.homologyMapIso (degreeComparison R L K) i ≪≫
    (K.sc i).mapHomologyIso (tensorRight L)

omit [HasDerivedCategory (Modules R)] in
set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_cycles (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (K : CochainComplex (Modules R) ℤ) (i : ℤ) :
    ∃ z : ((termwiseRight R L).obj K).cycles i ≅ K.cycles i ⊗ L,
      z.hom ≫ (K.iCycles i ▷ L) = ((termwiseRight R L).obj K).iCycles i ∧
      ((termwiseRight R L).obj K).homologyπ i ≫
          HomologicalComplex.homologyMap (degreeComparison R L K).inv i ≫
          (cohomologyComparison R L hL K i).hom = z.hom ≫ (K.homologyπ i ▷ L) := by
  obtain ⟨hl, hc⟩ := flat_exact R L hL
  have := hl
  have := hc
  refine ⟨(K.sc i).mapCyclesIso (tensorRight L),
    ShortComplex.mapCyclesIso_hom_iCycles _ _, ?_⟩
  dsimp only [cohomologyComparison, Iso.trans_hom, HomologicalComplex.homologyMapIso]
  erw [← HomologicalComplex.homologyMap_comp_assoc, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (K.sc i).leftHomologyData]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  simp only [ShortComplex.LeftHomologyData.map_π, ShortComplex.leftHomologyData_H,
    Functor.flip_obj_map, curriedTensor_map_app,
    ShortComplex.LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv]
  rw [← comp_whiskerRight]
  rfl

omit [HasDerivedCategory (Modules R)] in
set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_naturality
    (L L' : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (hL' : IsFlatOnSite (J := J) (R := R) L')
    (K K' : CochainComplex (Modules R) ℤ) (f : K ⟶ K') (g : L ⟶ L') (i : ℤ) :
    HomologicalComplex.homologyMap (totalMap R f g) i ≫
        (cohomologyComparison R L' hL' K' i).hom =
      (cohomologyComparison R L hL K i).hom ≫
        (HomologicalComplex.homologyMap f i ⊗ₘ g) := by
  obtain ⟨hl, hc⟩ := flat_exact R L hL
  have := hl
  have := hc
  obtain ⟨hl', hc'⟩ := flat_exact R L' hL'
  have := hl'
  have := hc'
  have hn := collapse_naturality (curriedTensor (Modules R)) g f
  have hh := congrArg (fun t ↦ HomologicalComplex.homologyMap t i) hn
  dsimp only [cohomologyComparison, Iso.trans_hom, HomologicalComplex.homologyMapIso]
  simp only [HomologicalComplex.homologyMap_comp] at hh
  erw [← Category.assoc, hh]
  simp only [Category.assoc]
  have ht := ShortComplex.homologyMap_mapNatTrans (K'.sc i)
    ((curriedTensor (Modules R)).flip.map g)
  have ht' :
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (Modules R)).flip.map g)
            (.up ℤ)).app K') i ≫ ((K'.sc i).mapHomologyIso (tensorRight L')).hom =
        ((K'.sc i).mapHomologyIso (tensorRight L)).hom ≫ (K'.homology i ◁ g) := by
    change ShortComplex.homologyMap ((K'.sc i).mapNatTrans
      ((curriedTensor (Modules R)).flip.map g)) ≫ _ = _
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  erw [ht']
  rw [← Category.assoc]
  have hf := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (Modules R) (.up ℤ) i).map f) (tensorRight L)
  change HomologicalComplex.homologyMap ((termwiseRight R L).map f) i ≫
    ((K'.sc i).mapHomologyIso (tensorRight L)).hom =
      ((K.sc i).mapHomologyIso (tensorRight L)).hom ≫
        (HomologicalComplex.homologyMap f i ▷ L) at hf
  simp only [Category.assoc]
  erw [reassoc_of% hf]
  simp [tensorHom_def]

set_option allowUnsafeReducibility true in
attribute [local irreducible] totalTensor ordinaryTensor
attribute [local irreducible] cohomologyComparison

private theorem resolving_ext
    {F : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R)}
    {H : CochainComplex (Modules R) ℤ ⥤ DerivedCategory (Modules R)}
    (α β : DerivedCategory.Q ⋙ F ⟶ H)
    (h : ∀ (P : CochainComplex (Modules R) ℤ)
      (_hk : CochainComplex.IsKFlatIndependentCoefficients P)
      (_hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)), α.app P = β.app P) :
    α = β := by
  ext K
  obtain ⟨P, p, hk, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  have := hp
  apply (cancel_epi (F.map (DerivedCategory.Q.map p))).1
  change (DerivedCategory.Q ⋙ F).map p ≫ _ = (DerivedCategory.Q ⋙ F).map p ≫ _
  rw [α.naturality, β.naturality]
  rw [h P hk (fun n ↦ (CategoryTheory.exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R _).symm (hf n))]

set_option backward.isDefEq.respectTransparency false in
private theorem object_comparison
    (hs : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L →
      CochainComplex.IsKFlatIndependentCoefficients ((degreeZero R).obj L) ∧
        ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (((degreeZero R).obj L).X n)) :
    ∃ a : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L →
        (DerivedCategory.Q ⋙ derivedRight R L ≅ totalRight R L ⋙ DerivedCategory.Q),
      (∀ (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
        (P : CochainComplex (Modules R) ℤ)
        (hk : CochainComplex.IsKFlatIndependentCoefficients P)
        (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)),
        (a L hL).app P =
          (representativeIso R P ((degreeZero R).obj L) hk (hs L hL).1
            hf (hs L hL).2).symm) ∧
      (∀ (L L' : Modules R)
        (hL : IsFlatOnSite (J := J) (R := R) L)
        (hL' : IsFlatOnSite (J := J) (R := R) L') (g : L ⟶ L')
        (K : CochainComplex (Modules R) ℤ),
        (a L hL).hom.app K ≫ DerivedCategory.Q.map (totalMap R (𝟙 K) g) =
          derivedMap R (𝟙 (DerivedCategory.Q.obj K)) g ≫ (a L' hL').hom.app K) := by
  classical
  obtain ⟨s, hs'⟩ := kFlat_fixed_tensor_triangulated R
  have ha (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L) :
      ∃ a : DerivedCategory.Q ⋙ derivedRight R L ≅ totalRight R L ⋙ DerivedCategory.Q,
      ∀ (P : CochainComplex (Modules R) ℤ)
        (hk : CochainComplex.IsKFlatIndependentCoefficients P)
        (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)),
        a.app P = (representativeIso R P ((degreeZero R).obj L) hk (hs L hL).1
          hf (hs L hL).2).symm := by
    obtain ⟨c, _, hc⟩ := (hs' _ (hs L hL).1 (hs L hL).2).2.2.2.2.1
    exact ⟨c.symm, fun P hk hf ↦ congrArg Iso.symm (hc P hk hf)⟩
  choose a ha using ha
  refine ⟨a, ha, ?_⟩
  intro L L' hL hL' g K
  let τ := (totalTensor R).flip.map ((degreeZero R).map g)
  let σ := (derivedTensor R).flip.map (DerivedCategory.Q.map ((degreeZero R).map g))
  let α := (a L hL).hom ≫ Functor.whiskerRight τ DerivedCategory.Q
  let β := Functor.whiskerLeft DerivedCategory.Q σ ≫ (a L' hL').hom
  have he : α = β := by
    apply resolving_ext R
    intro P hk hf
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [show (a L hL).hom.app P =
        (representativeIso R P ((degreeZero R).obj L) hk (hs L hL).1
          hf (hs L hL).2).inv from congrArg Iso.hom (ha L hL P hk hf)]
    rw [show (a L' hL').hom.app P =
        (representativeIso R P ((degreeZero R).obj L') hk (hs L' hL').1
          hf (hs L' hL').2).inv from congrArg Iso.hom (ha L' hL' P hk hf)]
    obtain ⟨c, _, hc⟩ := (hs' P hk hf).2.2.2.1
    have hn := c.inv.naturality ((degreeZero R).map g)
    change _ ≫ (c.app _).inv = (c.app _).inv ≫ _ at hn
    rw [hc _ (hs L hL).1 (hs L hL).2,
      hc _ (hs L' hL').1 (hs L' hL').2] at hn
    exact hn.symm
  have hh := congr_app he K
  simpa only [α, β, τ, σ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedMap_right, totalMap_right] using hh

omit [HasDerivedCategory (Modules R)] in
private def cohomologyNatIso (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) (i : ℤ) :
    totalRight R L ⋙ HomologicalComplex.homologyFunctor (Modules R) (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (Modules R) (.up ℤ) i ⋙ tensorRight L :=
  NatIso.ofComponents (fun K ↦ cohomologyComparison R L hL K i) (fun f ↦ by
    change HomologicalComplex.homologyMap ((totalRight R L).map f) i ≫ _ =
      _ ≫ (HomologicalComplex.homologyMap f i ▷ L)
    simpa only [totalMap_left, tensorHom_id, tensorHom_def, whiskerLeft_id,
      Category.comp_id] using
      cohomology_naturality R L L hL hL _ _ f (𝟙 L) i)

private def localizedComparison (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (a : DerivedCategory.Q ⋙ derivedRight R L ≅ totalRight R L ⋙ DerivedCategory.Q)
    (i : ℤ) :
    DerivedCategory.Q ⋙ (derivedRight R L ⋙
      DerivedCategory.homologyFunctor (Modules R) i) ≅
    DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor (Modules R) i ⋙ tensorRight L) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight a (DerivedCategory.homologyFunctor (Modules R) i) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (totalRight R L)
      (DerivedCategory.homologyFunctorFactors (Modules R) i) ≪≫
    cohomologyNatIso R L hL i ≪≫ Functor.isoWhiskerRight
      (DerivedCategory.homologyFunctorFactors (Modules R) i).symm (tensorRight L) ≪≫
    Functor.associator _ _ _

private def derivedCohomologyIso (L : Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L)
    (a : DerivedCategory.Q ⋙ derivedRight R L ≅ totalRight R L ⋙ DerivedCategory.Q)
    (i : ℤ) :
    derivedRight R L ⋙ DerivedCategory.homologyFunctor (Modules R) i ≅
      DerivedCategory.homologyFunctor (Modules R) i ⋙ tensorRight L :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) _ _ _ _
    (localizedComparison R L hL a i)

set_option backward.isDefEq.respectTransparency false in
private theorem derived_cohomology_comparison
    (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
    (a : DerivedCategory.Q ⋙ derivedRight R L ≅ totalRight R L ⋙ DerivedCategory.Q)
    (i : ℤ) :
    ∀ K : CochainComplex (Modules R) ℤ,
      (DerivedCategory.homologyFunctor (Modules R) i).map (a.hom.app K) ≫
          (DerivedCategory.homologyFunctorFactors (Modules R) i).hom.app
            ((totalRight R L).obj K) ≫ (cohomologyComparison R L hL K i).hom =
        (derivedCohomologyIso R L hL a i).hom.app (DerivedCategory.Q.obj K) ≫
          ((DerivedCategory.homologyFunctorFactors (Modules R) i).hom.app K ▷ L) := by
  intro K
  dsimp only [derivedCohomologyIso]
  erw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    Category.comp_id, Category.id_comp]
  dsimp only [localizedComparison, cohomologyNatIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Functor.flip_obj_map,
    curriedTensor_map_app]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  erw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight, Category.comp_id]

attribute [local irreducible] derivedCohomologyIso localizedComparison cohomologyNatIso

set_option backward.isDefEq.respectTransparency false in
/-- Flat single-term tensor, its derived-object model, and the canonical cohomology
comparisons, natural in arbitrary maps in both variables. The cycle inclusion and cycle
quotient equations characterize the cohomology map, rather than merely asking for some
isomorphism. The last equation normalizes it on every flat-term K-flat resolution,
so the same comparison is obtained independently of that resolution.

Source: Stacks Project, sites-cohomology.tex, Tags 06YN, 06YS and 06YU (construction
preceding definition-derived-tor); homology.tex, Tag 010N.
(blueprint: lem-fd-ringed-flat-single-tensor-cohomology)

Proof:
1. In Tot(K tensor L[0]), only the (n,0) summand survives in degree n. Its inclusion
   and projection are inverse, and its differential is d_K tensor 1. This is exactly
   degreeComparison. Tensor additivity and bifunctoriality come from
   lem-pc-sheaf-modules-tensor-closed and def-pc-tensor-complex-sheaves.
2. Flatness is exactness of right tensor (def-pc-flat-sheaf-modules). Apply
   lem-weil-pbc-exact-functor-complex-cohomology to its cycles, boundaries and quotient.
   Compose with degreeComparison to obtain c, with the two displayed cycle equations.
3. For any g:L→L' between flat sheaves, tensor with g is a natural transformation.
   Cancel the monic cycle inclusion to compare the cycle maps; then cancel the epic
   cycle quotient to compare the homology maps. This gives naturality in g without
   requiring g to be mono, epi or invertible, and combines with naturality in K.
4. If K is acyclic then c identifies all homology of Tot(K tensor L[0]) with zero.
   Thus L[0] is K-flat by def-pc-kflat-complex. Its other terms are zero and hence
   flat, by additive exactness of the zero tensor functor. No degree bound is used.
5. Apply the right-factor assertion of lem-trf-site-one-sided-tensor-normalization
   to L[0], obtaining a, normalized by the inverse of the two-sided comparison from
   lem-weil-pbc-site-derived-tensor-descent. Its naturality includes maps of L.
   Apply cohomology and compose with c. Parts (2) and (3) of
   lem-weil-pbc-localization-universal-property uniquely extend this isomorphism
   and its inverse to D(R), and extend the g-naturality square to every derived map.
6. For any flat-term K-flat resolution p:P→K, naturality of a and c gives the last
   equation. The model comparison is representativeIso followed by Qp tensor 1.
   Such resolutions exist for every unbounded K by lem-pc-kflat-resolution. Since
   gamma is a single natural isomorphism, the equation proves independence of all
   choices of resolution without needing a chain map between resolutions.
-/
theorem ringed_flat_single_tensor_cohomology
    {S : Type u} [Category.{v} S] [EssentiallySmall.{r} S]
    {J : GrothendieckTopology S} (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Modules R)] :
    ∃ hs : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L →
        CochainComplex.IsKFlatIndependentCoefficients ((degreeZero R).obj L) ∧
          ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (((degreeZero R).obj L).X n),
    ∃ a : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L →
        ((DerivedCategory.Q ⋙ derivedRight R L) ≅ (totalRight R L ⋙ DerivedCategory.Q)),
    ∃ c : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L →
        ∀ (K : CochainComplex (Modules R) ℤ) (i : ℤ),
          ((totalRight R L).obj K).homology i ≅ K.homology i ⊗ L,
    ∃ gamma : ∀ (L : Modules R), IsFlatOnSite (J := J) (R := R) L → ∀ i : ℤ,
        ((derivedRight R L ⋙ DerivedCategory.homologyFunctor (Modules R) i) ≅
          (DerivedCategory.homologyFunctor (Modules R) i ⋙ tensorRight L)),
      (∀ (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
          (P : CochainComplex (Modules R) ℤ)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P)
          (hPf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
        (a L hL).app P =
          (representativeIso R P ((degreeZero R).obj L) hP (hs L hL).1
            hPf (hs L hL).2).symm) ∧
      (∀ (L L' : Modules R)
          (hL : IsFlatOnSite (J := J) (R := R) L)
          (hL' : IsFlatOnSite (J := J) (R := R) L')
          (g : L ⟶ L') (K : CochainComplex (Modules R) ℤ),
        (a L hL).hom.app K ≫ DerivedCategory.Q.map (totalMap R (𝟙 K) g) =
          derivedMap R (𝟙 (DerivedCategory.Q.obj K)) g ≫ (a L' hL').hom.app K) ∧
      (∀ (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
          (K : CochainComplex (Modules R) ℤ) (i : ℤ),
        ∃ z : ((termwiseRight R L).obj K).cycles i ≅ K.cycles i ⊗ L,
          z.hom ≫ (K.iCycles i ▷ L) = ((termwiseRight R L).obj K).iCycles i ∧
          ((termwiseRight R L).obj K).homologyπ i ≫
              HomologicalComplex.homologyMap (degreeComparison R L K).inv i ≫
              (c L hL K i).hom = z.hom ≫ (K.homologyπ i ▷ L)) ∧
      (∀ (L L' : Modules R)
          (hL : IsFlatOnSite (J := J) (R := R) L)
          (hL' : IsFlatOnSite (J := J) (R := R) L')
          (K K' : CochainComplex (Modules R) ℤ) (f : K ⟶ K') (g : L ⟶ L') (i : ℤ),
        HomologicalComplex.homologyMap (totalMap R f g) i ≫ (c L' hL' K' i).hom =
          (c L hL K i).hom ≫ (HomologicalComplex.homologyMap f i ⊗ₘ g)) ∧
      (∀ (L L' : Modules R)
          (hL : IsFlatOnSite (J := J) (R := R) L)
          (hL' : IsFlatOnSite (J := J) (R := R) L')
          (g : L ⟶ L') (K : DerivedCategory (Modules R)) (i : ℤ),
        (DerivedCategory.homologyFunctor (Modules R) i).map (derivedMap R (𝟙 K) g) ≫
            (gamma L' hL' i).hom.app K =
          (gamma L hL i).hom.app K ≫
            (𝟙 ((DerivedCategory.homologyFunctor (Modules R) i).obj K) ⊗ₘ g)) ∧
      (∀ (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
          (K : CochainComplex (Modules R) ℤ) (i : ℤ),
        (DerivedCategory.homologyFunctor (Modules R) i).map ((a L hL).hom.app K) ≫
            (DerivedCategory.homologyFunctorFactors (Modules R) i).hom.app
              ((totalRight R L).obj K) ≫ (c L hL K i).hom =
          (gamma L hL i).hom.app (DerivedCategory.Q.obj K) ≫
            ((DerivedCategory.homologyFunctorFactors (Modules R) i).hom.app K ▷ L)) ∧
      (∀ (L : Modules R) (hL : IsFlatOnSite (J := J) (R := R) L)
          (P K : CochainComplex (Modules R) ℤ) (p : P ⟶ K) (_hp : QuasiIso p)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P)
          (hPf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) (i : ℤ),
        (DerivedCategory.homologyFunctor (Modules R) i).map
            ((representativeIso R P ((degreeZero R).obj L) hP (hs L hL).1
                hPf (hs L hL).2).hom ≫ derivedMap R (DerivedCategory.Q.map p) (𝟙 L)) ≫
            (gamma L hL i).hom.app (DerivedCategory.Q.obj K) =
          (DerivedCategory.homologyFunctorFactors (Modules R) i).hom.app
              ((totalRight R L).obj P) ≫ (c L hL P i).hom ≫
            (HomologicalComplex.homologyMap p i ▷ L) ≫
            ((DerivedCategory.homologyFunctorFactors (Modules R) i).inv.app K ▷ L))  := by
  classical
  let hs := single_properties R
  obtain ⟨a, ha, han⟩ := object_comparison R hs
  let gamma := fun L hL i ↦ derivedCohomologyIso R L hL (a L hL) i
  have hgamma := fun L hL i ↦ derived_cohomology_comparison R L hL (a L hL) i
  refine ⟨hs, a, cohomologyComparison R, gamma, ha, han,
    cohomology_cycles R, cohomology_naturality R, ?_,
    (fun L hL K i ↦ hgamma L hL i K), ?_⟩
  · intro L L' hL hL' g K i
    let H := DerivedCategory.homologyFunctor (Modules R) i
    let σ := (derivedTensor R).flip.map (DerivedCategory.Q.map ((degreeZero R).map g))
    let τ := (curriedTensor (Modules R)).flip.map g
    let α := Functor.whiskerRight σ H ≫ (gamma L' hL' i).hom
    let β := (gamma L hL i).hom ≫ Functor.whiskerLeft H τ
    have he : α = β := by
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
      intro E
      dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app]
      let h := DerivedCategory.homologyFunctorFactors (Modules R) i
      apply (cancel_mono (h.hom.app E ▷ L')).1
      have hn := han L L' hL hL' g E
      rw [derivedMap_right] at hn
      have hc := cohomology_naturality R L L' hL hL' E E (𝟙 E) g i
      simp only [HomologicalComplex.homologyMap_id, id_tensorHom] at hc
      have ht := τ.naturality (h.hom.app E)
      change (h.hom.app E ▷ L) ≫ (E.homology i ◁ g) =
        (H.obj (DerivedCategory.Q.obj E) ◁ g) ≫ (h.hom.app E ▷ L') at ht
      calc
        _ = H.map (σ.app (DerivedCategory.Q.obj E)) ≫
            (H.map ((a L' hL').hom.app E) ≫ h.hom.app ((totalRight R L').obj E) ≫
              (cohomologyComparison R L' hL' E i).hom) := by
          erw [Category.assoc, ← hgamma L' hL' i E]
        _ = H.map ((a L hL).hom.app E) ≫
            H.map (DerivedCategory.Q.map (totalMap R (𝟙 E) g)) ≫
            h.hom.app ((totalRight R L').obj E) ≫
            (cohomologyComparison R L' hL' E i).hom := by
          erw [← H.map_comp_assoc, ← hn, H.map_comp, Category.assoc]
        _ = H.map ((a L hL).hom.app E) ≫
            h.hom.app ((totalRight R L).obj E) ≫
            (cohomologyComparison R L hL E i).hom ≫ (E.homology i ◁ g) := by
          erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
          erw [hc]
        _ = _ := by
          erw [reassoc_of% (hgamma L hL i E)]
          simp only [Category.assoc]
          erw [ht]
          rfl
    have hh := congr_app he K
    simpa only [α, β, H, σ, τ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, derivedMap_right, id_tensorHom,
      curriedTensor_obj_map, Functor.flip_map_app] using hh
  · intro L hL P K p hp hP hPf i
    let H := DerivedCategory.homologyFunctor (Modules R) i
    let h := DerivedCategory.homologyFunctorFactors (Modules R) i
    have hn := (gamma L hL i).hom.naturality (DerivedCategory.Q.map p)
    have haP := congrArg Iso.inv (ha L hL P hP hPf)
    dsimp only [Iso.symm_inv] at haP
    erw [← haP, derivedMap_left, H.map_comp, Category.assoc]
    change H.map ((a L hL).inv.app P) ≫
      (H.map ((derivedRight R L).map (DerivedCategory.Q.map p)) ≫
        (gamma L hL i).hom.app (DerivedCategory.Q.obj K)) = _
    change H.map ((derivedRight R L).map (DerivedCategory.Q.map p)) ≫
      (gamma L hL i).hom.app (DerivedCategory.Q.obj K) =
      (gamma L hL i).hom.app (DerivedCategory.Q.obj P) ≫
        (H.map (DerivedCategory.Q.map p) ▷ L) at hn
    erw [hn, ← Category.assoc]
    have hP' := hgamma L hL i P
    have hP'' : H.map ((a L hL).inv.app P) ≫
        (gamma L hL i).hom.app (DerivedCategory.Q.obj P) =
      h.hom.app ((totalRight R L).obj P) ≫
        (cohomologyComparison R L hL P i).hom ≫ (h.inv.app P ▷ L) := by
      apply (cancel_epi (H.map ((a L hL).hom.app P))).1
      simp only [← H.map_comp_assoc, Iso.hom_inv_id_app, H.map_id, Category.id_comp]
      erw [reassoc_of% hP']
      dsimp only [h]
      erw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight, Category.comp_id]
    erw [hP'', Category.assoc, Category.assoc]
    congr 2
    have hh := h.inv.naturality p
    change HomologicalComplex.homologyMap p i ≫ h.inv.app K =
      h.inv.app P ≫ H.map (DerivedCategory.Q.map p) at hh
    rw [← comp_whiskerRight, ← hh, comp_whiskerRight]

end SheafOfModules.FlatSingleTensor
