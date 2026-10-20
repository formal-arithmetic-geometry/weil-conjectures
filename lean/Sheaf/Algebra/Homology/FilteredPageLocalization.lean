/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic
import Sheaf.Algebra.Homology.FilteredQuasiIsoFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Construction
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.BoundedFilteredComplexPageCore
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Localization of finite filtered pages

Source: Stacks Project, Homology, Tags 012K, 012M, 012O, 012P and 012W, and
Derived Categories, Tags 05S1 and 05S2
(blueprint: lem-kun-filtered-page-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The localization D_f(R) of the finite filtered homotopy category at graded
quasi-isomorphisms. Source: Stacks, Tag 05S2.
(blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredModuleDerivedCategory (R : Type u) [CommRing R] :=
  (CochainComplex.finiteFilteredModuleQuasiIso R).Localization

/-- The canonical localization functor from H_f(R) to D_f(R).
Source: Stacks, Tag 05S2.
(blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredModuleLocalizationFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleHomotopy R ⥤
      finiteFilteredModuleDerivedCategory R :=
  (CochainComplex.finiteFilteredModuleQuasiIso R).Q

/-- The actual quotient descent of the inclusion F^p into F^(p-r+1).
Source: Stacks, Tag 012K, quotient-image formula.
(blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredPageTransition (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (p r : ℤ) (hr : 1 ≤ r) :
    U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
      U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) := by
  let F := U.obj.filtration
  let ha : p - r + 1 ≤ p := by omega
  let hb : p + 1 ≤ p + r := by omega
  let hs : p ≤ p + r := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
  let ht : p - r + 1 ≤ p + 1 := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
  let i : (F.step p : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      (F.step (p - r + 1) : CochainComplex (ModuleCat.{u} R) ℤ) :=
    Subobject.ofLE _ _ (F.antitone_step ha)
  let k : (F.step (p + r) : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      (F.step p : CochainComplex (ModuleCat.{u} R) ℤ) :=
    Subobject.ofLE _ _ (F.antitone_step hs)
  let hz : k ≫ i ≫ F.complexQuotientπ (p - r + 1) (p + 1) ht = 0 := by
    dsimp [k, i, DecreasingFiltration.complexQuotientπ]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    rw [← Subobject.ofLE_comp_ofLE (F.step (p + r)) (F.step (p + 1))
      (F.step (p - r + 1)) (F.antitone_step hb) (F.antitone_step ht)]
    simp only [Category.assoc, cokernel.condition, comp_zero]
  exact cokernel.desc k (i ≫ F.complexQuotientπ (p - r + 1) (p + 1) ht) hz

/-- The quotient projection characterizes the transition. Source: Stacks, Tag 012K.
Proof: unfold the cokernel descent and apply cokernel.π_desc. This is Step 1 of the node.
(blueprint: lem-kun-filtered-page-localization). -/
theorem finiteFilteredPageTransition_projection (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (p r : ℤ) (hr : 1 ≤ r) :
    U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫
        finiteFilteredPageTransition R U p r hr =
      Subobject.ofLE (U.obj.filtration.step p)
          (U.obj.filtration.step (p - r + 1))
          (U.obj.filtration.antitone_step (by omega)) ≫
        U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) := by
  exact cokernel.π_desc _ _ _

/-- The page functor chosen together with its normalized successor maps, first-page
and image comparisons from lem-kun-filtered-page-functor-normalized.
Source: Stacks, Tags 012M and 012O.
(blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredPageFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤
      CohomologicalSpectralSequence (ModuleCat.{u} R) 1 :=
  (boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦ finiteFilteredPageTransition_projection R U p r hr)).choose

/-- The first-page comparison chosen with the normalized functor.
Source: Stacks, Tag 012M (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredPageFirstIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
    (((finiteFilteredPageFunctor R).obj U).page 1).X (a, b) ≅
      (U.obj.filtration.gradedPiece a).homology (a + b) :=
  (boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦ finiteFilteredPageTransition_projection R U p r hr)).choose_spec.choose U a b

/-- The core image comparison, chosen in the same normalized witness as the functor.
Source: Stacks, Tag 012K (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredPageImageIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
      image (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht)
        (a + b)) :=
  ((boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦
      finiteFilteredPageTransition_projection R U p r hr)).choose_spec.choose_spec).choose
    U a b t ht

/-- Cohomology of the underlying complex.
Source: Stacks, Tag 012P (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredModuleCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ ModuleCat.{u} R where
  obj U := U.obj.obj.homology n
  map f := HomologicalComplex.homologyMap f.hom.hom n
  map_id U := HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n

/-- The image step I^a_n inside ordinary cohomology.
Source: Stacks, Tag 012P (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredCohomologyImage (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) :
    Subobject (U.obj.obj.homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)

/-- Consecutive image steps are decreasing. Source: Stacks, Tag 012P,
filtration-cohomology equation (blueprint: lem-kun-filtered-page-localization).
Proof (Step 5): the inclusion F^(a+1) -> U factors through F^a -> U. Apply cohomology;
the image of a composite is contained in the image of the second arrow. -/
theorem finiteFilteredCohomologyImage_succ_le (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) :
    finiteFilteredCohomologyImage R U (a + 1) n ≤ finiteFilteredCohomologyImage R U a n := by
  unfold finiteFilteredCohomologyImage
  simpa only [← HomologicalComplex.homologyMap_comp, Subobject.ofLE_arrow] using
    imageSubobject_comp_le
      (HomologicalComplex.homologyMap
        (Subobject.ofLE _ _ (U.obj.filtration.F_succ_le a)) n)
      (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)

/-- The actual decreasing image filtration on cohomology, constructed from its inclusions.
Source: Stacks, Tag 012P (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredCohomologyFiltration (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ) :
    DecreasingFiltration (U.obj.obj.homology n) where
  F a := finiteFilteredCohomologyImage R U a n
  F_succ_le a := finiteFilteredCohomologyImage_succ_le R U a n

/-- The cohomology functor with its full image filtration; maps use the canonical image map.
Source: Stacks, Tags 012O and 012P (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ FilteredObject (ModuleCat.{u} R) where
  obj U := ⟨U.obj.obj.homology n, finiteFilteredCohomologyFiltration R U n⟩
  map {U V} f :=
    { hom := HomologicalComplex.homologyMap f.hom.hom n
      preserves := fun a ↦ by
        let sq : Arrow.mk (HomologicalComplex.homologyMap
            (U.obj.filtration.step a).arrow n) ⟶
            Arrow.mk (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) :=
          Arrow.homMk (HomologicalComplex.homologyMap
            (FilteredObject.restrictionSteps f.hom a) n)
            (HomologicalComplex.homologyMap f.hom.hom n) (by
              dsimp only [Arrow.mk_hom]
              rw [← HomologicalComplex.homologyMap_comp,
                ← HomologicalComplex.homologyMap_comp]
              congr 1
              exact Classical.choose_spec (f.hom.preserves a))
        exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩ }
  map_id U := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n

/-- Forget the filtration of a module.
Source: Stacks, Tag 012P (blueprint: lem-kun-filtered-page-localization). -/
def finiteFilteredCohomologyForget (R : Type u) [CommRing R] :
    FilteredObject (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj U := U.obj
  map f := f.hom

/-- Forget the filtration of a complex.
Source: Stacks, Tag 05S3 (blueprint: lem-kun-filtered-page-localization). -/
def finiteFilteredComplexForget (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj U := U.obj.obj
  map f := f.hom.hom

/-- The functor from filtered complexes to D_f(R).
Source: Stacks, Tag 05S2 (blueprint: lem-kun-filtered-page-localization). -/
def finiteFilteredDerivedQuotient (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ finiteFilteredModuleDerivedCategory R :=
  CochainComplex.finiteFilteredModuleHomotopyQuotient R ⋙
    finiteFilteredModuleLocalizationFunctor R

/-- The standard chosen derived category of modules; no extra size hypothesis is required.
Source: Stacks, Tag 05RU (blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredOrdinaryDerivedCategory (R : Type u) [CommRing R] :=
  @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)

/-- The ordinary derived localization for the standard chosen category.
Source: Stacks, Tag 05RU (blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredOrdinaryQ (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ finiteFilteredOrdinaryDerivedCategory R :=
  @DerivedCategory.Q (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)

/-- Ordinary derived cohomology in the standard chosen category.
Source: Stacks, Tag 05RU (blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredOrdinaryH (R : Type u) [CommRing R] (n : ℤ) :
    finiteFilteredOrdinaryDerivedCategory R ⥤ ModuleCat.{u} R :=
  @DerivedCategory.homologyFunctor (ModuleCat.{u} R) _ _
    (HasDerivedCategory.standard _) n

/-- The standard comparison between derived and cochain cohomology.
Source: Stacks, Tag 05RU (blueprint: lem-kun-filtered-page-localization). -/
abbrev finiteFilteredOrdinaryHComparison (R : Type u) [CommRing R] (n : ℤ) :
    finiteFilteredOrdinaryQ R ⋙ finiteFilteredOrdinaryH R n ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n :=
  @DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) _ _
    (HasDerivedCategory.standard _) n

/-- The ambient quotient U/F^(a+1), formed from the inclusion into U.
Source: Stacks, Tag 012K (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredAmbientQuotient (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  cokernel (U.obj.filtration.step (a + 1)).arrow

/-- The actual chain map F^a U to U/F^(a+1), as opposed to the graded projection.
Source: Stacks, Tag 012K (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredAmbientMap (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ) :
    (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      finiteFilteredAmbientQuotient R U a :=
  (U.obj.filtration.step a).arrow ≫ cokernel.π (U.obj.filtration.step (a + 1)).arrow

/-- The stationary image in H^n(U/F^(a+1)).
Source: Stacks, Tags 012K and 012W (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredQuotientImage (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) : ModuleCat.{u} R :=
  image (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n)

/-- The canonical map from the target quotient window to the ambient quotient.
Source: Stacks, Tag 012K (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredWindowToAmbient (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a t : ℤ) (ht : 1 ≤ t) :
    U.obj.filtration.complexQuotient (a - t + 1) (a + 1) (by omega) ⟶
      finiteFilteredAmbientQuotient R U a :=
  cokernel.desc _ ((U.obj.filtration.step (a - t + 1)).arrow ≫
    cokernel.π (U.obj.filtration.step (a + 1)).arrow) (by
      rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition])

/-- The map on ambient quotient complexes induced by a filtered chain map.
Source: Stacks, Tag 012O (blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredAmbientQuotientMap (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a : ℤ) :
    finiteFilteredAmbientQuotient R U a ⟶ finiteFilteredAmbientQuotient R V a :=
  cokernel.map _ _ (FilteredObject.restrictionSteps f.hom (a + 1)) f.hom.hom
    (Classical.choose_spec (f.hom.preserves (a + 1))).symm

/-- Transport a descended functor map to its specified cochain representatives.
This is conjugation by the descent comparison, so it also handles localized morphisms
without chain-map representatives. Source: Stacks, Tag 04VK
(blueprint: lem-kun-filtered-page-localization). -/
noncomputable def finiteFilteredDescendedMap (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C]
    (F : CochainComplex.FiniteFilteredModuleComplex R ⥤ C)
    (Fbar : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ Fbar ≅ F)
    {U V : CochainComplex.FiniteFilteredModuleComplex R}
    (α : (finiteFilteredDerivedQuotient R).obj U ⟶
      (finiteFilteredDerivedQuotient R).obj V) : F.obj U ⟶ F.obj V :=
  e.inv.app U ≫ Fbar.map α ≫ e.hom.app V

/-- A stationary comparison is fixed by the core image square and by both representative
normalizations. The last two equations express x ↦ [x] mod I^(a+1) and its inverse, on
H^n(F^a U); composing with the epic cycles-to-cohomology map gives the literal cycle
formulation. Source: Stacks, Tags 012K, 012P and 012W
(blueprint: lem-kun-filtered-page-localization). -/
structure FilteredPageStationaryComparison (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) where
  pageToImage : (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
    finiteFilteredQuotientImage R U a (a + b)
  core_normalization :
    pageToImage.hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) =
      (finiteFilteredPageImageIso R U a b t ht).hom ≫
        image.ι (HomologicalComplex.homologyMap
          (finiteFilteredPageTransition R U a t ht) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R U a t ht) (a + b)
  imageToGraded : finiteFilteredQuotientImage R U a (a + b) ≅
    (finiteFilteredCohomologyFiltration R U (a + b)).gradedPiece a
  representative_forward :
    factorThruImage (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a)
        (a + b)) ≫ imageToGraded.hom =
      factorThruImageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a))
  representative_inverse :
    factorThruImageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) ≫
        imageToGraded.inv =
      factorThruImage (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a)
        (a + b))

/-- Full descent and stationary-comparison data, with every map specified by its chain
representatives and the localization universal property. The fields use the existing
filtered-object category, so their step and graded maps are its canonical restrictions and
cokernel maps. Source: Stacks, Tags 012K, 012M, 012O, 012P, 012W, 05S2, 05S3 and 04VK
(blueprint: lem-kun-filtered-page-localization). -/
structure FilteredPageLocalizationData (R : Type u) [CommRing R] where
  Sbar : finiteFilteredModuleDerivedCategory R ⥤
    CohomologicalSpectralSequence (ModuleCat.{u} R) 1
  eS : finiteFilteredDerivedQuotient R ⋙ Sbar ≅ finiteFilteredPageFunctor R
  Hbar : ℤ → finiteFilteredModuleDerivedCategory R ⥤ FilteredObject (ModuleCat.{u} R)
  eH : ∀ n : ℤ,
    finiteFilteredDerivedQuotient R ⋙ Hbar n ≅ finiteFilteredCohomology R n
  omega : finiteFilteredModuleDerivedCategory R ⥤ finiteFilteredOrdinaryDerivedCategory R
  eOmega : finiteFilteredDerivedQuotient R ⋙ omega ≅
    finiteFilteredComplexForget R ⋙ finiteFilteredOrdinaryQ R
  ordinaryCohomology : ∀ n : ℤ,
    Hbar n ⋙ finiteFilteredCohomologyForget R ≅ omega ⋙ finiteFilteredOrdinaryH R n
  ordinary_normalization : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ),
    (ordinaryCohomology n).hom.app ((finiteFilteredDerivedQuotient R).obj U) ≫
        (finiteFilteredOrdinaryH R n).map (eOmega.hom.app U) ≫
        (finiteFilteredOrdinaryHComparison R n).hom.app U.obj.obj =
      ((eH n).hom.app U).hom
  gradedDerived : ℤ → finiteFilteredModuleDerivedCategory R ⥤
    finiteFilteredOrdinaryDerivedCategory R
  gradedComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ),
    (gradedDerived a).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      (finiteFilteredOrdinaryQ R).obj (U.obj.filtration.gradedPiece a)
  graded_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a : ℤ),
    (gradedDerived a).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (gradedComparison V a).hom =
      (gradedComparison U a).hom ≫
        (finiteFilteredOrdinaryQ R).map (FilteredObject.gradedMapSteps f.hom a)
  page_one : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V) (a b : ℤ),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) Sbar eS α).hom 1).f
        (a, b) ≫ (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).inv.app
          (U.obj.filtration.gradedPiece a) ≫
        (finiteFilteredOrdinaryH R (a + b)).map
          ((gradedComparison U a).inv ≫ (gradedDerived a).map α ≫
            (gradedComparison V a).hom) ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).hom.app
          (V.obj.filtration.gradedPiece a)
  page_one_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) ≫
        (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom a) (a + b)
  homotopy_invariance : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f g : U ⟶ V), CochainComplex.finiteFilteredModuleHomotopyRel R f g →
    (finiteFilteredPageFunctor R).map f = (finiteFilteredPageFunctor R).map g ∧
    ∀ n : ℤ,
      HomologicalComplex.homologyMap f.hom.hom n =
        HomologicalComplex.homologyMap g.hom.hom n ∧
      (finiteFilteredCohomology R n).map f = (finiteFilteredCohomology R n).map g ∧
      ∀ a : ℤ,
        FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map g) a ∧
        FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map g) a
  quasiIso_representatives : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V), CochainComplex.finiteFilteredModuleQuasiIso R
        ((CochainComplex.finiteFilteredModuleHomotopyQuotient R).map f) →
    QuasiIso f.hom.hom ∧
    (∀ a : ℤ, QuasiIso (FilteredObject.restrictionSteps f.hom a)) ∧
    ∀ n : ℤ,
      IsIso (HomologicalComplex.homologyMap f.hom.hom n) ∧
      IsIso ((finiteFilteredCohomology R n).map f) ∧
      ∀ a : ℤ,
        IsIso (FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a) ∧
        IsIso (FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a)
  quasiIso_pages : ∀ {K L : CochainComplex.FiniteFilteredModuleHomotopy R}
      (w : K ⟶ L), CochainComplex.finiteFilteredModuleQuasiIso R w →
    IsIso (Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)) ∧
    ∀ (t : ℤ) (ht : 1 ≤ t),
      IsIso ((Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)).hom t ht)
  imageDerived : ℤ → ℤ → finiteFilteredModuleDerivedCategory R ⥤ ModuleCat.{u} R
  imageComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ),
    (imageDerived a b).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      finiteFilteredQuotientImage R U a (a + b)
  image_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (imageComparison U a b).inv ≫
        (imageDerived a b).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (imageComparison V a b).hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)) =
      image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b)
  bound : CochainComplex.FiniteFilteredModuleComplex R → ℤ → ℤ → ℤ
  stationary_window : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ), bound U a b ≤ t →
    U.obj.filtration.step (a + t) = ⊥ ∧ U.obj.filtration.step (a - t + 1) = ⊤
  comparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t), bound U a b ≤ t →
    FilteredPageStationaryComparison R U a b t ht
  stationary_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) Sbar eS α).hom t ht).f
        (a, b) ≫ (comparison V a b t ht hV).pageToImage.hom =
      (comparison U a b t ht hU).pageToImage.hom ≫
        (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
          (imageComparison V a b).hom
  stationary_graded_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
        (imageComparison V a b).hom ≫ (comparison V a b t ht hV).imageToGraded.hom =
      (comparison U a b t ht hU).imageToGraded.hom ≫
        FilteredObject.gradedMapSteps
          (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
            (Hbar (a + b)) (eH (a + b)) α) a
  successor_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        (comparison U a b t ht hU).pageToImage.hom =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
        (comparison U a b (t + 1) (by omega) (by omega)).pageToImage.hom
  successor_graded_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (comparison U a b t ht hU).imageToGraded =
      (comparison U a b (t + 1) (by omega) (by omega)).imageToGraded

/-- Filtered pages, filtered cohomology and the normalized stationary image abutment descend
to D_f(R). Bidegrees (a,b) cover the node's (a,n-a) by b=n-a. There is no cochain-degree bound.
Source: Stacks, Tags 012K, 012M, 012O, 012P, 012W, 05S1, 05S2, 05S3 and 04VK
(blueprint: lem-kun-filtered-page-localization).

Proof, following all eleven steps of the node:
1. Use lem-kun-filtered-page-functor-normalized with the actual quotient descent phi.
   The projection equation fixes phi uniquely; retain its first-page, image and normalized
   successor witnesses, so the chosen core comparison cannot be replaced by an arbitrary iso.
2. Restrict a filtered homotopy to each step and graded complex. For cycles x, the difference
   is d(hx), giving equality on cohomology. The natural first-page comparison and the
   spectral-sequence successor equation give equality on every positive page. Restriction
   and passage to cokernels give equality on every I step and successive quotient.
3. For a representative w of W filter Cone(w) componentwise. Its graded pieces are
   Cone(gr(w)), acyclic by lem-pur-quasi-iso-cone-acyclic. Filter each step of the cone by
   max(i,a); lem-sp-degreewise-filtered-acyclic and the cone criterion show that every
   F^a(w) is a quasi-isomorphism. At a common whole step this proves the underlying claim.
4. The page-one map is H(gr(w)); induction through successor homology gives page isos.
   Inverting components gives an inverse spectral-sequence morphism.
5. The cohomology inclusion square defines the image maps. For w both vertical maps are
   bijections, so the restriction to images is bijective, as are their quotients. Inclusion
   factorizations make I decreasing; whole and zero steps give finite bounds.
6. Apply lem-weil-pbc-localization-universal-property to pages and filtered cohomology.
   Forgetting filtration and taking gr give omega and gradedDerived into D(R), since they
   preserve homotopies and invert W. Uniqueness of localization identifies Hbar with ordinary
   derived cohomology, with the displayed normalization. Descend the page-one comparison.
7. Choose filtration bounds ell,h. For t at least max(1,h-a,a-ell+1), the source window
   identifies with F^a and the target with U/F^(a+1). The core image comparison gives
   pageToImage with its displayed square. Write C=F^a intersect ker d, D=F^(a+1) intersect
   ker d and B=F^a intersect im d. The kernel of C to H(U/F^(a+1)) is D+B.
8. The kernel of C to I^a is B and the inverse image of I^(a+1) is D+B. Hence both image
   objects are C/(D+B). This defines imageToGraded with the forward and inverse equations
   on H(F^a), equivalently on cycle representatives after its epic class projection.
9. For a filtered chain map both comparisons send the representative x to f(x), giving the
   two naturality squares. At adjacent stationary pages the cycles and boundaries are
   constant and the normalized successor sends x to x. This gives successor_agreement
   and successor_graded_agreement with the actual chosen successor isomorphism.
10. Use lem-kun-filtered-quasi-isomorphism-fractions and the opposite-category form of
    lem-pc-left-localization-fraction-representation to express a derived morphism by a roof.
    Choose a larger index stationary also for its middle object. Invert the W leg in the
    chain-map squares. Descend to every index stationary for the endpoints using Step 9 and
    the spectral-sequence morphism equation. Localization uniqueness gives independence of
    the roof and the induced functor image maps, recorded by image_chain.
11. Every bound is on filtration indices, uniformly over cochain degrees. For a above the
    zero bound or below the whole bound the stationary quotients are zero. The zero complex
    and zero ring satisfy the same calculations. No cochain-degree bound is used. -/
theorem filteredPageLocalization (R : Type u) [CommRing R] :
    Nonempty (FilteredPageLocalizationData R) := by
  sorry

end CategoryTheory
