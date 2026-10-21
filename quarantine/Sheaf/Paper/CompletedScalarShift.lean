/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.CompletedScalarChainShift
import Sheaf.Paper.CompletedScalarShiftDescent
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Completed scalar extension and cochain shifts

Source: the blueprint of the Weil conjectures, `def-weil-finite-coefficient-point`,
final equivalence display (blueprint: lem-weil-point-completed-scalar-shift).
The representative sign calculation uses Stacks Project Tags 011G, 014E and 08TC.
The coordinates below are mapping-cocone coordinates: the first is detected by
`mappingCocone.fst` and the second by `mappingCocone.snd`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {L : Type u} [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The canonical tensor reindexing at a finite level, followed by scalar restriction.
Both comparisons are the `mapCochainComplexShiftIso` comparisons of the underlying
additive module functors; no tower isomorphism is chosen.
Source: Stacks Tags 011G and 08TC (blueprint: lem-weil-point-completed-scalar-shift). -/
noncomputable def completedScalarShiftLevelIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) (n : ℕ) :
    (integralScalarLevel l E L ι Y n).obj (P⟦m⟧) ≅
      ((integralScalarLevel l E L ι Y n).obj P)⟦m⟧ :=
  (integralOperationsRestrict l L Y n).mapIso
      (((integralScalarReduction l E L ι Y n).mapCochainComplexShiftIso m).app P) ≪≫
    ((SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).mapCochainComplexShiftIso
            m).app
      ((integralScalarFiniteComplex l E L ι Y n).obj P)

/-- The canonical degreewise product reindexing, fixed at every quotient level.
Source: Stacks Tags 011G and 08TC (blueprint: lem-weil-point-completed-scalar-shift). -/
noncomputable def completedScalarShiftProductIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj (P⟦m⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))⟦m⟧ :=
  Limits.Pi.mapIso (fun n ↦ completedScalarShiftLevelIso ι Y P m n) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex (integralTowerModules l L Y) ℤ) m)
      (fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))).symm

/-- The two coordinates of the actual Roos shift map. The first inclusion carries
coefficient one, and the second carries `(-1)^m`. These are inclusions in the
mapping *cocone*, rather than in the unshifted mapping cone.
Source: Stacks Tags 011G, 014E and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftConeFormula
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) : Prop :=
  (∀ j : ℤ,
    (CochainComplex.mappingCocone.inl
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).v j j (by omega) ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      (completedScalarShiftProductIso ι Y P m).hom.f j ≫
        (CochainComplex.mappingCocone.inl
          (completedScalarRoosEndomorphism l E L ι Y P)).v (j + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv) ∧
  (∀ (i j : ℤ) (h : i + 1 = j),
    (CochainComplex.mappingCocone.inr
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).1.v i j h ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      m.negOnePow • ((completedScalarShiftProductIso ι Y P m).hom.f i ≫
        (CochainComplex.mappingCocone.inr
          (completedScalarRoosEndomorphism l E L ι Y P)).1.v
            (i + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv))

/-- The chain equation, with the standard degreewise tensor identification.
Source: Stacks Tags 011G and 014E (blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftChainEquation
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        ((completedScalarChainComparison l E L ι Y).app P)⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        (Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y) (self := eC) m).hom.app P

/-- Normalization of ordinary derived shift by the universal counit on good complexes.
Source: Stacks Tags 011G, 06YT and 06YU
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftOrdinaryNormalization
    (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    (Functor.commShiftIso (completedDerivedScalarExtension l E L ι Y) (self := eE) m).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
        (completedScalarCounit l E L ι Y P.obj)⟦m⟧' =
      (completedDerivedScalarExtension l E L ι Y).map
          ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
        completedScalarCounit l E L ι Y (P.obj⟦m⟧) ≫
        DerivedCategory.Q.map
          (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app
            P.obj) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app
          ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)

/-- The strict derived shift is the descent of this same chain alpha, with the
retained localization comparison. Shifted representatives remain good.
Source: Stacks Tags 011G, 06YS and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftIntegralNormalization
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    ∃ hP : integralOperationsGoodComplex l E Y (P.obj⟦m⟧),
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y) (self := eL) m).hom.app
            (DerivedCategory.Q.obj P.obj) ≫
          ((integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P)⟦m⟧' =
        (integralScalarExtensionOfUniverses l E L ι Y).map
            ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app
            ⟨P.obj⟦m⟧, hP⟩ ≫
          DerivedCategory.Q.map
            ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
              (self := eC) m).hom.app P.obj) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app
            ((integralScalarComplexFunctor l E L ι Y).obj P.obj)

/-- The fixed cone formula, chain equation, and normalized descended shift square.
The chain CommShift supplies naturality and the standard zero/successive laws
for exactly the same alpha used in all these clauses.
Source: Stacks Tags 011G, 014E, 06YS, 06YT and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftRepresentativeProperty
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ) : Prop := by
  exact
    (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
      completedScalarShiftConeFormula ι Y eC P m) ∧
    completedScalarShiftChainEquation ι Y eC ∧
    completedScalarShiftOrdinaryNormalization ι Y eE ∧
    completedScalarShiftIntegralNormalization ι Y eC eL ∧
    @NatTrans.CommShift _ _ _ _
      (completedDerivedScalarExtension l E L ι Y)
      (integralScalarExtensionOfUniverses l E L ι Y)
      (completedScalarComparison l E L ι Y) ℤ _ _ _ eE eL

attribute [-instance] SheafOfModules.instPreadditive in
private theorem homotopyCounitShift_exists
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive]
    (F : DerivedCategory (A) ⥤
      DerivedCategory (B))
    (ε : DerivedCategory.Qh ⋙ F ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hkan : F.IsRightKanExtension ε) :
    ∃ eF : F.CommShift ℤ,
      ∀ (P : CochainComplex (A) ℤ) (m : ℤ),
        (Functor.commShiftIso F (self := eF) m).hom.app (DerivedCategory.Q.obj P) ≫
          (ε.app ((HomotopyCategory.quotient (A) (.up ℤ)).obj P))⟦m⟧' =
        F.map ((DerivedCategory.Q.commShiftIso m).inv.app P) ≫
          ε.app ((HomotopyCategory.quotient (A) (.up ℤ)).obj (P⟦m⟧)) ≫
          DerivedCategory.Q.map ((G.mapCochainComplexShiftIso m).hom.app P) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app
            ((G.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨eE, hε⟩ := Functor.rightKanExtension_coherentShift _ DerivedCategory.Qh F ε hkan
  let := eE
  let := hε
  let q := HomotopyCategory.quotient A (.up ℤ)
  let i := DerivedCategory.quotientCompQhIso A
  let j := (Functor.associator q (G.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let δ : DerivedCategory.Q ⋙ F ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv F ≫
      (Functor.associator q DerivedCategory.Qh F).hom ≫
      Functor.whiskerLeft q ε ≫ j.hom
  have hδ : NatTrans.CommShift δ ℤ := by
    dsimp [δ, j, i, q]
    infer_instance
  let := hδ
  have hδapp (P : CochainComplex A ℤ) :
      δ.app P = ε.app (q.obj P) := by
    simp only [δ, j, i, q, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      CategoryTheory.Quotient.lift.isLift_hom, CategoryTheory.Quotient.lift.isLift_inv]
    erw [F.map_id, Category.id_comp]
    erw [(DerivedCategory.Qh (C := B)).map_id, Category.comp_id]
    exact Category.comp_id _
  refine ⟨eE, ?_⟩
  intro P m
  have h := NatTrans.shift_app_comm δ m P
  simp only [Functor.commShiftIso_comp_hom_app, hδapp, Category.assoc] at h
  apply (cancel_epi (F.map ((DerivedCategory.Q.commShiftIso m).hom.app P))).mp
  rw [← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
  simpa only [Functor.mapHomologicalComplex_commShiftIso_eq] using h

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted

attribute [-instance] SheafOfModules.instPreadditive in
private theorem ordinaryShift_exists :
    ∃ eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ,
      completedScalarShiftOrdinaryNormalization ι Y eE := by
  let G := completedOrdinaryScalarExtension l E L ι Y
  let F := completedDerivedScalarExtension l E L ι Y
  let ε : DerivedCategory.Qh ⋙ F ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose
  have hkan : F.IsRightKanExtension ε :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.1.1
  obtain ⟨eE, hE⟩ := homotopyCounitShift_exists G F ε hkan
  refine ⟨eE, ?_⟩
  intro P m
  have hh := hE P.obj m
  have heps (X : CochainComplex (integralTowerModules l E Y) ℤ) :
      completedScalarCounit l E L ι Y X = ε.app
        ((HomotopyCategory.quotient (integralTowerModules l E Y) (.up ℤ)).obj X) := by
    rfl
  rw [heps, heps]
  exact hh


attribute [local irreducible] completedDerivedScalarExtension
  completedOrdinaryScalarExtension
  completedScalarChainComparison completedScalarComparison
  integralScalarExtensionOfUniverses integralScalarExtensionComparisonOfUniverses

attribute [-instance] SheafOfModules.instPreadditive in
private theorem goodRepresentative_exists
    (K : DerivedCategory (integralTowerModules l E Y)) :
    ∃ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _) K
  obtain ⟨P, p, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) A
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E Y)
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E Y)
  have hp : integralOperationsGoodComplex l E Y P :=
    ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (P.X n)).symm (hf n)⟩
  have := hq
  exact ⟨⟨P, hp⟩, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

attribute [-instance] SheafOfModules.instPreadditive in
private theorem comparisonShift_of_normalizations
    (G : (integralTowerModules l E Y) ⥤ (integralTowerModules l L Y)) [G.Additive]
    (C : CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l L Y) ℤ) [C.CommShift ℤ]
    (F T : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y)) [F.CommShift ℤ] [T.CommShift ℤ]
    (b : G.mapHomologicalComplex (.up ℤ) ⟶ C) (χ : F ⟶ T)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ)
    (eP : T.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (C.obj P))
    (ePm : T.obj (DerivedCategory.Q.obj (P⟦m⟧)) ≅ DerivedCategory.Q.obj (C.obj (P⟦m⟧)))
    (cP : F.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (cPm : F.obj (DerivedCategory.Q.obj (P⟦m⟧)) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj (P⟦m⟧)))
    (hχP : χ.app (DerivedCategory.Q.obj P) ≫ eP.hom = cP ≫ DerivedCategory.Q.map (b.app P))
    (hχPm : χ.app (DerivedCategory.Q.obj (P⟦m⟧)) ≫ ePm.hom =
      cPm ≫ DerivedCategory.Q.map (b.app (P⟦m⟧)))
    (hC : (G.mapCochainComplexShiftIso m).hom.app P ≫ (b.app P)⟦m⟧' =
      b.app (P⟦m⟧) ≫ (C.commShiftIso m).hom.app P)
    (hE : (F.commShiftIso m).hom.app (DerivedCategory.Q.obj P) ≫ cP⟦m⟧' =
      F.map ((DerivedCategory.Q.commShiftIso m).inv.app P) ≫ cPm ≫
        DerivedCategory.Q.map ((G.mapCochainComplexShiftIso m).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (hL : (T.commShiftIso m).hom.app (DerivedCategory.Q.obj P) ≫ eP.hom⟦m⟧' =
      T.map ((DerivedCategory.Q.commShiftIso m).inv.app P) ≫ ePm.hom ≫
        DerivedCategory.Q.map ((C.commShiftIso m).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app (C.obj P)) :
    (F.commShiftIso m).hom.app (DerivedCategory.Q.obj P) ≫
      (χ.app (DerivedCategory.Q.obj P))⟦m⟧' =
    χ.app ((DerivedCategory.Q.obj P)⟦m⟧) ≫
      (T.commShiftIso m).hom.app (DerivedCategory.Q.obj P) := by
  apply (cancel_mono (eP.hom⟦m⟧')).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp, hχP, Functor.map_comp]
  rw [← Category.assoc, hE]
  rw [Category.assoc, hL]
  erw [← χ.naturality_assoc ((DerivedCategory.Q.commShiftIso m).inv.app P)]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hχPm]
  have hn := (DerivedCategory.Q.commShiftIso m).hom.naturality (b.app P)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← hn, ← DerivedCategory.Q.map_comp_assoc, hC, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]

attribute [-instance] SheafOfModules.instPreadditive in
set_option backward.isDefEq.respectTransparency false in
private theorem comparisonShift_onGood
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ)
    (hC : completedScalarShiftChainEquation ι Y eC)
    (hE : completedScalarShiftOrdinaryNormalization ι Y eE)
    (hL : completedScalarShiftIntegralNormalization ι Y eC eL)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ) :
    (Functor.commShiftIso (completedDerivedScalarExtension l E L ι Y)
        (self := eE) m).hom.app (DerivedCategory.Q.obj P.obj) ≫
      ((completedScalarComparison l E L ι Y).app (DerivedCategory.Q.obj P.obj))⟦m⟧' =
    (completedScalarComparison l E L ι Y).app ((DerivedCategory.Q.obj P.obj)⟦m⟧) ≫
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y)
        (self := eL) m).hom.app (DerivedCategory.Q.obj P.obj) := by
  let := eC
  let := eE
  let := eL
  let F := completedDerivedScalarExtension l E L ι Y
  let T := integralScalarExtensionOfUniverses l E L ι Y
  let χ := completedScalarComparison l E L ι Y
  let b := completedScalarChainComparison l E L ι Y
  let e := integralScalarExtensionComparisonOfUniverses l E L ι Y
  have hχ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      χ.app (DerivedCategory.Q.obj P.obj) ≫ e.hom.app P =
        completedScalarCounit l E L ι Y P.obj ≫ DerivedCategory.Q.map (b.app P.obj) := by
    change (completedScalarComparison l E L ι Y).app _ ≫ _ = _
    unfold completedScalarComparison
    exact (completedScalarComparison_existsUnique l E L ι Y).exists.choose_spec P
  obtain ⟨hP, hLP⟩ := hL P m
  let Pm : (integralOperationsGoodComplex l E Y).FullSubcategory := ⟨P.obj⟦m⟧, hP⟩
  exact comparisonShift_of_normalizations (l := l) (E := E) (L := L) Y
    (completedOrdinaryScalarExtension l E L ι Y)
    (integralScalarComplexFunctor l E L ι Y) F T b χ P.obj m
    (e.app P) (e.app Pm)
    (completedScalarCounit l E L ι Y P.obj)
    (completedScalarCounit l E L ι Y (P.obj⟦m⟧))
    (hχ P) (hχ Pm) (hC P.obj m) (hE P m) hLP

attribute [-instance] SheafOfModules.instPreadditive in
/-- The canonical completed scalar comparison commutes with every integer shift,
with its ordinary tensor and strict Roos comparisons normalized on representatives.
In particular this applies to every derived-complete input K and every good
representative of K, independently of its chosen resolution. The strict chain
comparison alpha has coordinates `(x,y) ↦ (x,(-1)^m y)` in the mapping cocone.
Source: the final equivalence display of the Weil blueprint and Stacks Project
Tags 011G, 014E, 06YS, 06YT, 06YU and 08TC
(blueprint: lem-weil-point-completed-scalar-shift).
Proof: choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Shift
preserves flat terms; the signed total-tensor reindexing preserves K-flatness.
The finite tensor and restriction shift maps are mapCochainComplexShiftIso, and
their product is completedScalarShiftProductIso. Quotient transitions commute
with this fixed reindexing. In mapping-cocone coordinates the source differential
is (e dx,-e dy-hx), the target differential is (e dx,-e dy-e hx), where e=(-1)^m.
The diagonal map (1,e) intertwines them and is its own inverse. Diagonal maps of
products show chain-level naturality. For zero shift its components are identities;
for successive shifts they multiply to (1,(-1)^(m+n)), giving the CommShift laws.
The quotient-map comparison has zero second component, so alpha chi_{P[m]} equals
chi_P[m] after the canonical tensor reindexing, as an equality of chain maps.
The equivalence of lem-weil-pbc-site-derived-tensor-descent and the quasi-isomorphism
invariance of lem-weil-integral-scalar-extension-well-defined descend these maps
and their coherences. Normalize ordinary derived shift by completedScalarCounit
and strict derived shift by integralScalarExtensionComparisonOfUniverses and
Q.map(alpha). The canonical-comparison uniqueness of
lem-weil-finite-free-completed-scalar-comparison identifies the descended chain
map with chi. The normalized chain equation then gives NatTrans.CommShift. -/
theorem completedScalarComparison_commutesWithShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t}) :
    ∃ (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
      (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ)
      (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ),
      completedScalarShiftRepresentativeProperty ι Y eC eE eL := by
  obtain ⟨eC, hcone, hC⟩ := completedScalarChainShift l E L ι Y
  have hproduct : completedScalarChainProductIso l E L ι Y =
      completedScalarShiftProductIso ι Y := rfl
  rw [hproduct] at hcone
  obtain ⟨eE, hE⟩ := ordinaryShift_exists ι Y
  obtain ⟨eL, hL⟩ := completedScalarShiftDescent l E L ι Y eC
  refine ⟨eC, eE, eL, hcone, hC, hE, hL, ?_⟩
  let := eC
  let := eE
  let := eL
  constructor
  intro m
  ext K
  obtain ⟨P, ⟨e⟩⟩ := goodRepresentative_exists (E := E) Y K
  have h := comparisonShift_onGood ι Y eC eE eL hC hE hL P m
  let F := completedDerivedScalarExtension l E L ι Y
  let T := integralScalarExtensionOfUniverses l E L ι Y
  let χ := completedScalarComparison l E L ι Y
  let α : shiftFunctor _ m ⋙ F ⟶ T ⋙ shiftFunctor _ m :=
    (F.commShiftIso m).hom ≫ Functor.whiskerRight χ (shiftFunctor _ m)
  let β : shiftFunctor _ m ⋙ F ⟶ T ⋙ shiftFunctor _ m :=
    Functor.whiskerLeft (shiftFunctor _ m) χ ≫ (T.commShiftIso m).hom
  change α.app K = β.app K
  apply (cancel_epi ((shiftFunctor _ m ⋙ F).map e.hom)).mp
  calc
    _ = α.app (DerivedCategory.Q.obj P.obj) ≫
        (T ⋙ shiftFunctor _ m).map e.hom := α.naturality e.hom
    _ = β.app (DerivedCategory.Q.obj P.obj) ≫
        (T ⋙ shiftFunctor _ m).map e.hom := congrArg (· ≫ _) h
    _ = _ := (β.naturality e.hom).symm

end WeilConjectures
