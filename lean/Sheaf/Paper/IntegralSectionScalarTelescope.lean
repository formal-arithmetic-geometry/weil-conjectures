/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import all Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Paper.ContinuousIntegralDerivedUnit
import Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.Paper.ContinuousIntegralComplexTelescope
import Sheaf.Paper.ContinuousIntegralLocalizationCounit
import Sheaf.Paper.ContinuousConstructibleIntegralImage
import all Sheaf.Algebra.Homology.InternalHomLocalizationComparison
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # The actual integral coefficient telescope in the section-module presentation

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the exact coefficient and section-module transport.
(blueprint: lem-sfb-integral-section-scalar-telescope).
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option linter.privateModule false
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Localization.Monoidal.instMonoidalCategoryLocalizedMonoidal
  CategoryTheory.Localization.Monoidal.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.homComplexFunctor
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Mod.extendScalars
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence
  CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
  CategoryTheory.InternalAbelianSheafModule.sectionScalarMap

universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transport_telescope
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Abelian A] [Abelian A'] [HasDerivedCategory A] [HasDerivedCategory A']
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} A']
    (e : A ≌ A') [e.functor.Additive] [e.inverse.Additive] (d : B ≌ B')
    {F : DerivedCategory A ⥤ B} {U : B ⥤ DerivedCategory A}
    {F' : DerivedCategory A' ⥤ B'} {U' : B' ⥤ DerivedCategory A'}
    (adj : F ⊣ U) (adj' : F' ⊣ U')
    (r : U ⋙ e.functor.mapDerivedCategory ≅ d.functor ⋙ U') (p : ℕ)
    (β : ∀ C : CochainComplex A ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 C))) ≅
        U.obj (F.obj (DerivedCategory.Q.obj C)))
    (hβ : ∀ C, DerivedCategory.Q.map
      (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 C)) 0) ≫ (β C).hom =
        adj.unit.app (DerivedCategory.Q.obj C)) :
    ∃ β' : ∀ P : CochainComplex A' ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P))) ≅
        U'.obj (F'.obj (DerivedCategory.Q.obj P)),
      ∀ P, DerivedCategory.Q.map
        (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) 0) ≫ (β' P).hom =
          adj'.unit.app (DerivedCategory.Q.obj P) := by
  let G := e.functor.mapDerivedCategory
  let GC := e.functor.mapHomologicalComplex (.up ℤ)
  let m := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ r.hom)).natTrans
  have : IsIso m := inverseMate_isIso adj adj' r
  let mi := asIso m
  let δ (X : DerivedCategory A) : G.obj (U.obj (F.obj X)) ≅
      U'.obj (F'.obj (G.obj X)) := r.app (F.obj X) ≪≫ U'.mapIso (mi.app X).symm
  have hδ (X : DerivedCategory A) : G.map (adj.unit.app X) ≫ (δ X).hom =
      adj'.unit.app (G.obj X) := by
    dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hu := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ r.hom) X
    change G.map (adj.unit.app X) ≫ (r.app (F.obj X)).hom =
      adj'.unit.app (G.obj X) ≫ U'.map (mi.app X).hom at hu
    rw [← Category.assoc, hu]
    simp only [Category.assoc, ← U'.map_comp, Iso.hom_inv_id, U'.map_id]
    exact Category.comp_id _
  have hP (P : CochainComplex A' ℤ) :
      ∃ b : DerivedCategory.Q.obj
          (colimit (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P))) ≅
            U'.obj (F'.obj (DerivedCategory.Q.obj P)),
        DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) 0) ≫ b.hom =
            adj'.unit.app (DerivedCategory.Q.obj P) := by
    let C := (e.inverse.mapHomologicalComplex (.up ℤ)).obj P
    let q : GC.obj C ≅ P := (e.mapHomologicalComplex (.up ℤ)).counitIso.app P
    let D := Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 C)
    let D' := Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)
    let zt : D ⋙ GC ⟶ D' := NatTrans.ofSequence (fun _ ↦ q.hom) (by
      intro n
      dsimp only [D, D']
      simp only [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      change GC.map (p • 𝟙 C) ≫ q.hom = q.hom ≫ (p • 𝟙 P)
      rw [GC.map_nsmul, GC.map_id]
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id])
    let z : D ⋙ GC ≅ D' := NatIso.ofComponents (fun _ ↦ q)
      (fun _ ↦ zt.naturality _)
    let zc : colimit D' ≅ GC.obj (colimit D) :=
      (HasColimit.isoOfNatIso z).symm ≪≫ (preservesColimitIso GC D).symm
    have hz : colimit.ι D' 0 ≫ zc.hom = q.inv ≫ GC.map (colimit.ι D 0) := by
      dsimp only [zc, Iso.trans_hom, Iso.symm_hom]
      rw [← Category.assoc, HasColimit.isoOfNatIso_ι_inv]
      erw [Category.assoc, ι_preservesColimitIso_inv]
      rfl
    let f := e.functor.mapDerivedCategoryFactors
    let eP : G.obj (DerivedCategory.Q.obj C) ≅ DerivedCategory.Q.obj P :=
      f.app C ≪≫ DerivedCategory.Q.mapIso q
    let b0 : DerivedCategory.Q.obj (colimit D') ≅ G.obj (DerivedCategory.Q.obj (colimit D)) :=
      DerivedCategory.Q.mapIso zc ≪≫ (f.app (colimit D)).symm
    have hb0 : DerivedCategory.Q.map (colimit.ι D' 0) ≫ b0.hom =
        eP.inv ≫ G.map (DerivedCategory.Q.map (colimit.ι D 0)) := by
      dsimp only [b0, eP, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
        Functor.mapIso_hom, Functor.mapIso_inv]
      rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hz,
        DerivedCategory.Q.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun z ↦ DerivedCategory.Q.map q.inv ≫ z)
        (f.inv.naturality (colimit.ι D 0))
    let b := b0 ≪≫ G.mapIso (β C) ≪≫ δ (DerivedCategory.Q.obj C) ≪≫
      (F' ⋙ U').mapIso eP
    refine ⟨b, ?_⟩
    dsimp only [b, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hb0]
    simp only [Category.assoc]
    rw [← G.map_comp_assoc, hβ]
    rw [← Category.assoc (G.map (adj.unit.app (DerivedCategory.Q.obj C)))
      (δ (DerivedCategory.Q.obj C)).hom, hδ]
    change eP.inv ≫ adj'.unit.app _ ≫ (F' ⋙ U').map eP.hom = _
    rw [← adj'.unit.naturality eP.hom]
    simp only [Functor.id_map, Iso.inv_hom_id_assoc]
  choose β' hβ' using hP
  exact ⟨β', hβ'⟩

private theorem full_transport
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    (e : A ≌ A') (d : B ≌ B') (U : B ⥤ A) (V : B' ⥤ A') [U.Full]
    (r : U ⋙ e.functor ≅ d.functor ⋙ V) : V.Full := by
  constructor
  intro X Y f
  let x := d.inverse.obj X
  let y := d.inverse.obj Y
  let f' := V.map (d.counitIso.app X).hom ≫ f ≫ V.map (d.counitIso.app Y).inv
  let g := e.functor.preimage ((r.app x).hom ≫ f' ≫ (r.app y).inv)
  let h := U.preimage g
  refine ⟨(d.counitIso.app X).inv ≫ d.functor.map h ≫ (d.counitIso.app Y).hom, ?_⟩
  have hh : e.functor.map (U.map h) = (r.app x).hom ≫ f' ≫ (r.app y).inv := by
    rw [U.map_preimage, e.functor.map_preimage]
  have hr := r.hom.naturality h
  change e.functor.map (U.map h) ≫ (r.app y).hom =
    (r.app x).hom ≫ V.map (d.functor.map h) at hr
  rw [hh] at hr
  have hv : V.map (d.functor.map h) = f' := by
    apply (cancel_epi (r.app x).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hr.symm
  rw [V.map_comp, V.map_comp, hv]
  dsimp only [f']
  simp only [Category.assoc, ← V.map_comp_assoc, Iso.inv_hom_id, V.map_id,
    Category.id_comp, ← V.map_comp, Iso.inv_hom_id, Category.comp_id]

private theorem scalar_reflect_equivalence
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (e : A ≌ B) [e.inverse.Additive] (p : ℕ)
    (hp : ∀ T : A, IsIso (p • 𝟙 T)) (T : B) : IsIso (p • 𝟙 T) := by
  have h := hp (e.inverse.obj T)
  have : IsIso (e.inverse.map (p • 𝟙 T)) := by
    rw [e.inverse.map_nsmul, e.inverse.map_id]
    exact h
  exact isIso_of_reflects_iso _ e.inverse

private theorem colimit_unit_iso
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    (D : ℕ ⥤ A) [HasColimit D] {T : A} {Y : B} (unit : D.obj 0 ⟶ T)
    (eta : Q.obj (D.obj 0) ⟶ Y)
    (ht : ∃ c : Cocone D, Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ T, c.ι.app 0 ≫ e.hom = unit)
    (hu : ∃ eu : Q.obj T ≅ Y, Q.map unit ≫ eu.hom = eta) :
    ∃ b : Q.obj (colimit D) ≅ Y,
      Q.map (colimit.ι D 0) ≫ b.hom = eta := by
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := ht
  obtain ⟨eu, heu⟩ := hu
  let ec' := colimit.isoColimitCocone ⟨c, hc⟩ ≪≫ ec
  refine ⟨Q.mapIso ec' ≪≫ eu, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Q.map_comp]
  have hz : colimit.ι D 0 ≫ ec'.hom = unit := by
    dsimp only [ec', Iso.trans_hom]
    rw [← Category.assoc, colimit.isoColimitCocone_ι_hom]
    exact hec
  rw [hz]
  exact heu

namespace AlgebraicGeometry.ProEtale

attribute [local instance 2000] Mod.isGrothendieckAbelian
  hasSmallestColimitsOfHasColimits Limits.instHasColimitOfHasColimitsOfShape


/-- The canonical small Grothendieck-derived localization for section modules.
Source: Stacks 07A5, via the existing Grothendieck module-sheaf construction.
(blueprint: lem-sfb-integral-section-scalar-telescope). -/
noncomputable local instance integralSectionScalarDerived (X : Scheme.{u})
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1, u + 1, u + 2}
        (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R) :=
  fun R ↦ HasDerivedCategory.ofIsGrothendieckAbelian
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R)

private theorem native_telescope_unit
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u}) :
    let φ := coefficientMap (CondensedRing.integralScalarMap l E) X
    let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
    let ad := Mod.derivedExtendMapDerivedCategoryAdjunction φ
    ∃ β : ∀ C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff l E) X)) ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 C))) ≅
        U.mapDerivedCategory.obj
          ((CondensedRing.integralScalarExtension l E X).obj (DerivedCategory.Q.obj C)),
      ∀ C, DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 C)) 0) ≫ (β C).hom =
        ad.unit.app (DerivedCategory.Q.obj C) := by
  classical
  intro φ U ad
  have hβ (C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff l E) X)) ℤ) :
      ∃ b : DerivedCategory.Q.obj
          (colimit (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 C))) ≅
            U.mapDerivedCategory.obj
          ((CondensedRing.integralScalarExtension l E X).obj (DerivedCategory.Q.obj C)),
        DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 C)) 0) ≫ b.hom =
            ad.unit.app (DerivedCategory.Q.obj C) := by
    have ht := CondensedRing.integralComplexLocalization_colimit l E X C
    have hu := CondensedRing.integralScalar_derivedUnit_complex l E X C
    exact colimit_unit_iso DerivedCategory.Q
      (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 C))
      (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app C)
      (ad.unit.app (DerivedCategory.Q.obj C)) ht hu
  choose β hβ using hβ
  exact ⟨β, hβ⟩

private theorem native_section_scalar_telescope
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E] (X : Scheme.{u})
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (s : ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (coefficientMap (CondensedRing.integralScalarMap l E) X))) :
    let a := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (coefficientMap (CondensedRing.integralScalarMap l E) X)
    (∀ T : DerivedCategory (scalarModules.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E) X)),
      IsIso (l • 𝟙 T)) ∧
    (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).Full ∧
    ∃ β : ∀ P : CochainComplex (scalarModules.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (CondensedRing.integralCoeff l E) X)) ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 P))) ≅
        (scalarDerivedRestriction a).obj (s.derived.obj (DerivedCategory.Q.obj P)),
      ∀ P, DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 P)) 0) ≫ (β P).hom =
        s.adjunction.unit.app (DerivedCategory.Q.obj P) := by
  classical
  let φ := coefficientMap (CondensedRing.integralScalarMap l E) X
  let L := Mod.extendScalars φ
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let adj := Mod.extendRestrictAdjunction φ
  have : PreservesFiniteLimits L := CondensedRing.integralScalarExtension_exact l E X
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : PreservesFiniteColimits L := inferInstance
  let ad := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let eR := ModuleObjectRingedComparison.equivalence (CondensedRing.integralCoeff l E) X
  let eS := ModuleObjectRingedComparison.equivalence (Profinite.continuousMapRingObj E) X
  let r0 := scalarRestrictionIso (Scheme.ProEt.topology X) φ
  let r := (Functor.mapDerivedCategoryCompIso U eR.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso r0 ≪≫
      Functor.mapDerivedCategoryCompIso eS.functor
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) φ))
  have hb := native_telescope_unit l E X
  let β := hb.choose
  have hβ := hb.choose_spec
  let a := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) φ
  have hU : scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a =
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory := by
    unfold scalarDerivedRestriction Functor.mapDerivedCategory
    rfl
  let r' : U.mapDerivedCategory ⋙ eR.functor.mapDerivedCategory ≅
      eS.functor.mapDerivedCategory ⋙ scalarDerivedRestriction a :=
    r ≪≫ Functor.isoWhiskerLeft eS.functor.mapDerivedCategory (eqToIso hU.symm)
  have ht := transport_telescope eR eS.mapDerivedCategory
    ad s.adjunction r' l β hβ
  let β' := ht.choose
  have hβ' := ht.choose_spec
  have hu : ∀ P, IsIso (adj.counit.app P) :=
    CondensedRing.integralScalarCounit_isIso l E X
  have : IsIso adj.counit :=
    (NatTrans.isIso_iff_isIso_app adj.counit).mpr hu
  have : U.Full := adj.fullyFaithfulROfIsIsoCounit.full
  have : U.Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
  have : U.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  let hff : U.rightDerivedFunctor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  have : U.mapDerivedCategory.Full :=
    (hff.ofIso U.rightDerivedFunctorIsoMapDerivedCategory).full
  have : eS.mapDerivedCategory.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact scalar_reflect_equivalence eS.mapDerivedCategory l
      (CondensedRing.derived_nsmul_isIso l E X) T
  · rw [hU]
    exact full_transport eR.mapDerivedCategory eS.mapDerivedCategory U.mapDerivedCategory _ r
  · exact ⟨β', hβ'⟩


/-- The actual integral inclusion is a reflective scalar localization, computed on
all complexes by the repeated-ell telescope, with the specified derived unit.

Source: Bhatt--Scholze, Lemma 6.8.2; Stacks, Tags 03CY and 07A6.
(blueprint: lem-sfb-integral-section-scalar-telescope).

Proof. Multiplication by ell is invertible on continuous E-modules. The ordinary
integral extension unit is the filtered colimit of repeated multiplication by ell,
degree by degree. Its exactness identifies ordinary and derived extension on all
complexes and identifies their units. Restriction is fully faithful: the inverse
scalar action forces every integral-linear map between E-modules to be E-linear.
Transport the ordinary and derived adjunctions through the exact internal-module
and section-module equivalences. Uniqueness of left adjoints identifies extension
with the specified scalar pair and preserves the unit normalization. Equivalences
preserve the complex telescope colimit, giving the asserted beta isomorphisms. -/
theorem integralSectionScalarTelescope
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u})
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (s : ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (padicIntegersToPadicSubfield.{u} X l E))) :
    let a := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (padicIntegersToPadicSubfield.{u} X l E)
    (∀ T : DerivedCategory (scalarModules.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)),
      IsIso (l • 𝟙 T)) ∧
    (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).Full ∧
    ∃ β : ∀ P : CochainComplex (scalarModules.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X)) ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 P))) ≅
        (scalarDerivedRestriction a).obj (s.derived.obj (DerivedCategory.Q.obj P)),
      ∀ P, DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 P)) 0) ≫ (β P).hom =
        s.adjunction.unit.app (DerivedCategory.Q.obj P) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  let : NormedAlgebra ℚ_[l] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl l) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact native_section_scalar_telescope l E.1 X s

end AlgebraicGeometry.ProEtale
