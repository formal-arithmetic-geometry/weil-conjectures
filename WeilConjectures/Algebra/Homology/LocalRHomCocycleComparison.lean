/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LocalRHomDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.LocalRHom.Cocycle

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]


/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
abbrev A := Mod.{uC, vC, u} J R

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
abbrev evaluation (U : C) :=
  SheafOfModules.forget (rings.{uC, vC, u} J R) ⋙
    PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
      forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U))) AddCommGrpCat

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
abbrev sectionComplex (L I : CochainComplex (A.{uC, vC, u} J R) ℤ) (U : C) :=
  ((evaluation.{uC, vC, u} J R U).mapHomologicalComplex (.up ℤ)).obj
    (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
set_option backward.isDefEq.respectTransparency true in
/-- The local Hom-complex comparison is additive and is specified on its representatives.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem homotopyComparison (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    (U : C) (n : ℤ) :
    let S := sectionComplex.{uC, vC, u} J R L I U
    let q := HomotopyCategory.quotient
      (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U)) (.up ℤ)
    ∃ (ec : S.cycles n ≃+
      CochainComplex.HomComplex.Cocycle
        ((complexRes.{uC, vC, u} J R U).obj L)
        ((complexRes.{uC, vC, u} J R U).obj I) n)
      (a : S.homology n ≃+
        (q.obj ((complexRes.{uC, vC, u} J R U).obj L) ⟶
          q.obj (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧))),
      (∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((ec z).val.v p q hpq).val.app W =
          (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
            L I n p q hpq).val.app (op U)) (S.iCycles n z)).app W) ∧
      ∀ z : S.cycles n, a (S.homologyπ n z) =
        q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (ec z)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R
  let := module_overFunctor_preservesZero.{uC, vC, max uC vC u, max uC vC u} R₀ U
  let res : CochainComplex (SheafOfModules.{max uC vC u} R₀) ℤ ⥤
      CochainComplex (SheafOfModules.{max uC vC u} (R₀.over U)) ℤ :=
    (SheafOfModules.overFunctor.{max uC vC u} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max uC vC u} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let S : CochainComplex AddCommGrpCat.{max uC vC u} ℤ :=
    E.obj (homComplex (R := R) L I)
  let T : CochainComplex AddCommGrpCat.{max uC vC u} ℤ :=
    CochainComplex.HomComplex (res.obj L) (res.obj I)
  let π := Classical.choose
    (homComplex_projections_exists.{uC, vC, max uC vC u, max uC vC u} (J := J) (R := R))
  have hco := homComplex_sections_cochainsOfUniverses.{uC, vC, u} (C := C) (J := J) R U L I
  dsimp only at hco
  obtain ⟨e, he⟩ := hco
  have hcomm := homComplex_sections_cochains_commOfUniverses.{uC, vC, u}
    (C := C) (J := J) R U L I
  dsimp only at hcomm
  have hd := hcomm e he
  let f : S ⟶ T :=
    { f := fun i ↦ AddCommGrpCat.ofHom (e i).toAddMonoidHom
      comm' := by
        intro i j hij
        ext x
        exact (hd i j hij x).symm }
  have hf (i : ℤ) : IsIso (f.f i) := by
    exact (AddEquiv.toAddCommGrpIso (X := S.X i) (Y := T.X i) (e i)).isIso_hom
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  let F := asIso f
  let h := CochainComplex.HomComplex.leftHomologyData (res.obj L) (res.obj I) n
  let ec := (HomologicalComplex.cyclesMapIso F n) ≪≫ h.cyclesIso
  let ac := (HomologicalComplex.homologyMapIso F n) ≪≫ h.homologyIso
  let a := ac.addCommGroupIsoToAddEquiv.trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
  refine ⟨ec.addCommGroupIsoToAddEquiv, a, ?_, ?_⟩
  · intro z p q hpq W
    have hc : (ec.hom z).val = e n (S.iCycles n z) := by
      have hh := ConcreteCategory.congr_hom
        (h.cyclesIso_hom_comp_i) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
      exact hh.trans hh'
    exact (congrArg (fun c ↦ (c.v p q hpq).val.app W) hc).trans
      (he n (S.iCycles n z) p q hpq W)
  · intro z
    have ha : ac.hom (S.homologyπ n z) =
        CochainComplex.HomComplex.CohomologyClass.mk (ec.hom z) := by
      have hh := ConcreteCategory.congr_hom
        (h.homologyπ_comp_homologyIso_hom) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality f n) z
      exact (congrArg h.homologyIso.hom hh').trans hh
    change CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (ac.hom (S.homologyπ n z)) = _
    exact (congrArg CochainComplex.HomComplex.CohomologyClass.homAddEquiv ha).trans
      (CochainComplex.HomComplex.CohomologyClass.toHom_mk (ec.hom z))



omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- Localizing the comparison into a restricted K-injective target.
Source: Stacks Project, Tags 0A94 and 070I.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem derivedComparison (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ) :
    let S := sectionComplex.{uC, vC, u} J R L I U
    ∃ (ec : S.cycles n ≃+
      CochainComplex.HomComplex.Cocycle
        ((complexRes.{uC, vC, u} J R U).obj L)
        ((complexRes.{uC, vC, u} J R U).obj I) n)
      (a : S.homology n ≃+
        (DerivedCategory.Q.obj ((complexRes.{uC, vC, u} J R U).obj L) ⟶
          DerivedCategory.Q.obj (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧))),
      (∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((ec z).val.v p q hpq).val.app W =
          (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
            L I n p q hpq).val.app (op U)) (S.iCycles n z)).app W) ∧
      ∀ z : S.cycles n, a (S.homologyπ n z) =
        DerivedCategory.Q.map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (ec z)) := by
  classical
  let S := sectionComplex.{uC, vC, u} J R L I U
  let q := HomotopyCategory.quotient
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U)) (.up ℤ)
  have hI : CochainComplex.IsKInjective ((complexRes.{uC, vC, u} J R U).obj I) :=
    isKInjective_restrict_localizedOfUniverses.{uC, vC, u} (rings.{uC, vC, u} J R) U
      (module_overFunctor_preservesZero _ _) I
  obtain ⟨ec, a, he, ha⟩ := homotopyComparison.{uC, vC, u} J R L I U n
  let b := AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective
      (q.obj ((complexRes.{uC, vC, u} J R U).obj L))
      (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧))
  let c := Iso.homCongr
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))).app
        ((complexRes.{uC, vC, u} J R U).obj L))
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))).app
        (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧))
  let c' : _ ≃+ _ :=
    { c with
      map_add' := by
        intro f g
        dsimp [c, Iso.homCongr]
        simp only [Preadditive.comp_add, Preadditive.add_comp] }
  refine ⟨ec, a.trans (b.trans c'), he, ?_⟩
  intro z
  change c (b (a (S.homologyπ n z))) = _
  rw [ha]
  change (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))).inv.app
        ((complexRes.{uC, vC, u} J R U).obj L) ≫
      DerivedCategory.Qh.map
        (q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (ec z))) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))).hom.app
          (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧) = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp only [Iso.inv_hom_id_app_assoc]

/-- The cocycle equivalence characterized by its component families.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
def cyclesEquiv (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ) :
    (sectionComplex.{uC, vC, u} J R L I U).cycles n ≃+
      CochainComplex.HomComplex.Cocycle
        ((complexRes.{uC, vC, u} J R U).obj L)
        ((complexRes.{uC, vC, u} J R U).obj I) n :=
  (derivedComparison.{uC, vC, u, wSlice} J R L I U n).choose

/-- The additive cohomology comparison characterized on cocycles by localization.
Source: Stacks Project, Tag 0A94.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
def cohomologyEquiv (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ) :
    (sectionComplex.{uC, vC, u} J R L I U).homology n ≃+
      (DerivedCategory.Q.obj ((complexRes.{uC, vC, u} J R U).obj L) ⟶
        DerivedCategory.Q.obj (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧)) :=
  (derivedComparison.{uC, vC, u, wSlice} J R L I U n).choose_spec.choose

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- The component characterization of the chosen cocycle comparison.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem cyclesEquiv_component (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : (sectionComplex.{uC, vC, u} J R L I U).cycles n)
    (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ) :
    (((cyclesEquiv.{uC, vC, u, wSlice} J R L I U n z).val.v p q hpq).val.app W) =
      (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
        L I n p q hpq).val.app (op U))
          ((sectionComplex.{uC, vC, u} J R L I U).iCycles n z)).app W :=
  (derivedComparison.{uC, vC, u, wSlice} J R L I U n).choose_spec.choose_spec.1
    z p q hpq W

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- The chosen cohomology comparison sends a cycle class to its localized chain map.
Source: Stacks Project, Tag 0A94.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem cohomologyEquiv_π (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : (sectionComplex.{uC, vC, u} J R L I U).cycles n) :
    cohomologyEquiv.{uC, vC, u, wSlice} J R L I U n
      ((sectionComplex.{uC, vC, u} J R L I U).homologyπ n z) =
        DerivedCategory.Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (cyclesEquiv.{uC, vC, u, wSlice} J R L I U n z)) :=
  (derivedComparison.{uC, vC, u, wSlice} J R L I U n).choose_spec.choose_spec.2 z

-- The comparison API fixes these data without reducing the construction proof.
attribute [irreducible] cyclesEquiv cohomologyEquiv

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- The component formula uniquely specifies the chosen cocycle equivalence.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem cyclesEquiv_unique (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (e : (sectionComplex.{uC, vC, u} J R L I U).cycles n ≃+
      CochainComplex.HomComplex.Cocycle ((complexRes.{uC, vC, u} J R U).obj L)
        ((complexRes.{uC, vC, u} J R U).obj I) n)
    (he : ∀ (z : (sectionComplex.{uC, vC, u} J R L I U).cycles n)
      (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
      ((e z).val.v p q hpq).val.app W =
        (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
          L I n p q hpq).val.app (op U))
            ((sectionComplex.{uC, vC, u} J R L I U).iCycles n z)).app W) :
    e = cyclesEquiv.{uC, vC, u, wSlice} J R L I U n := by
  apply AddEquiv.ext
  intro z
  apply CochainComplex.HomComplex.Cocycle.ext
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  ext W x
  exact congrArg (fun f ↦ f.hom x) ((he z p q hpq W).trans
    (cyclesEquiv_component.{uC, vC, u, wSlice} J R L I U n z p q hpq W).symm)

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- The cycle-class formula uniquely specifies the chosen derived cohomology equivalence.
Source: Stacks Project, Tag 0A94.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem cohomologyEquiv_unique (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (a : (sectionComplex.{uC, vC, u} J R L I U).homology n ≃+
      (DerivedCategory.Q.obj ((complexRes.{uC, vC, u} J R U).obj L) ⟶
        DerivedCategory.Q.obj (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧)))
    (ha : ∀ z : (sectionComplex.{uC, vC, u} J R L I U).cycles n,
      a ((sectionComplex.{uC, vC, u} J R L I U).homologyπ n z) =
        DerivedCategory.Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (cyclesEquiv.{uC, vC, u, wSlice} J R L I U n z))) :
    a = cohomologyEquiv.{uC, vC, u, wSlice} J R L I U n := by
  apply AddEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    ((sectionComplex.{uC, vC, u} J R L I U).homologyπ n)).mp inferInstance x
  exact (ha z).trans (cohomologyEquiv_π.{uC, vC, u, wSlice} J R L I U n z).symm

/-- The actual chain map of a cycle, with restriction and shifting in the specified order.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
def cycleMap (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : (sectionComplex.{uC, vC, u} J R L I U).cycles n) :
    (complexRes.{uC, vC, u} J R U).obj L ⟶
      (complexRes.{uC, vC, u} J R U).obj (I⟦n⟧) :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (cyclesEquiv.{uC, vC, u, wSlice} J R L I U n z) ≫
    ((complexRes.{uC, vC, u} J R U).commShiftIso n).inv.app I

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- Each component of the local chain map is the corresponding Hom-complex projection.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem cycleMap_component (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : (sectionComplex.{uC, vC, u} J R L I U).cycles n)
    (p : ℤ) (W : (Over U)ᵒᵖ) :
    (((cycleMap.{uC, vC, u, wSlice} J R L I U n z).f p).val.app W) =
      (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
        L I n p (p + n) rfl).val.app (op U))
          ((sectionComplex.{uC, vC, u} J R L I U).iCycles n z)).app W := by
  change (((cyclesEquiv.{uC, vC, u, wSlice} J R L I U n z).val.v
    p (p + n) rfl).val.app W) = _
  exact cyclesEquiv_component.{uC, vC, u, wSlice} J R L I U n z p (p + n) rfl W

/-- Evaluation of a sheaf cycle as a cycle in the complex of sections.
Source: Stacks Project, Tag 03EI.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
def sectionCycle (L I : CochainComplex (A.{uC, vC, u} J R) ℤ) (U : C) (n : ℤ)
    (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u}
      (R := R) L I).cycles n).val.obj (op U)) :
    (sectionComplex.{uC, vC, u} J R L I U).cycles n := by
  let H := homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I
  let S := sectionComplex.{uC, vC, u} J R L I U
  refine (S.sc n).abCyclesIso.inv ⟨(H.iCycles n).val.app (op U) z, ?_⟩
  change ((H.d n ((ComplexShape.up ℤ).next n)).val.app (op U))
    ((H.iCycles n).val.app (op U) z) = 0
  exact congrArg (fun f ↦ f.val.app (op U) z)
    (H.iCycles_d n ((ComplexShape.up ℤ).next n))

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}] in
/-- Evaluating a cycle preserves its inclusion into the complex term.
Source: Stacks Project, Tag 03EI.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem sectionCycle_i (L I : CochainComplex (A.{uC, vC, u} J R) ℤ) (U : C) (n : ℤ)
    (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I).cycles n).val.obj (op U)) :
    (sectionComplex.{uC, vC, u} J R L I U).iCycles n
        (sectionCycle.{uC, vC, u} J R L I U n z) =
      ((homComplex.{uC, vC, max uC vC u, max uC vC u}
        (R := R) L I).iCycles n).val.app (op U) z := by
  dsimp only [sectionCycle]
  exact ShortComplex.abCyclesIso_inv_apply_iCycles _ _

/-- A sheaf cycle gives its concrete local chain map.
Source: Stacks Project, Tags 0A8Y and 0A94.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
def sheafCycleMap (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I).cycles n).val.obj (op U)) :
    (complexRes.{uC, vC, u} J R U).obj L ⟶
      (complexRes.{uC, vC, u} J R U).obj (I⟦n⟧) :=
  cycleMap.{uC, vC, u, wSlice} J R L I U n (sectionCycle.{uC, vC, u} J R L I U n z)

omit [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)] in
/-- The concrete local map has exactly the prescribed component family.
Source: Stacks Project, Tag 0A8Y.
(blueprint: lem-per-local-rhom-additive-cocycle-comparison). -/
theorem sheafCycleMap_component (L I : CochainComplex (A.{uC, vC, u} J R) ℤ)
    [I.IsKInjective] (U : C) (n : ℤ)
    (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u}
      (R := R) L I).cycles n).val.obj (op U)) (p : ℤ) (W : (Over U)ᵒᵖ) :
    (((sheafCycleMap.{uC, vC, u, wSlice} J R L I U n z).f p).val.app W) =
      (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R)
        L I n p (p + n) rfl).val.app (op U))
          (((homComplex.{uC, vC, max uC vC u, max uC vC u}
            (R := R) L I).iCycles n).val.app (op U) z)).app W := by
  simpa only [sheafCycleMap, sectionCycle_i] using
    cycleMap_component.{uC, vC, u, wSlice} J R L I U n
      (sectionCycle.{uC, vC, u} J R L I U n z) p W

end CategoryTheory.LocalRHom.Cocycle
