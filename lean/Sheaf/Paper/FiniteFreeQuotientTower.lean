/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Sheaf.Paper.FinitePowerComplex
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The basis comparison for the strict tower of quotient complexes

Source: Stacks Project, Modules on Sites, Tags 03CY, 03DA, 03DB and 03EK;
Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-free-quotient-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid traversing the large dependent tensor transports for tactic style linting.
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules
open scoped ChangeOfRings
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private instance tensorPreadditive (T : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (𝓡 T)) where
  whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
  zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
  whiskerLeft_add := fun {X _Y _Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight := fun {X _Y _Z} f g ↦ (tensorRight X).map_add (f := f) (g := g)

private instance quotientUnitInclusionIso (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    IsIso (koszulTensorUnitInclusion T P) := by
  have (k : ℤ) : IsIso ((koszulTensorUnitInclusion T P).f k) := by
    change IsIso ((λ_ (P.X k)).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso
        (MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T)))
          (SheafOfModules.unit (𝓡 T)) P k).inv)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

@[irreducible] private def quotientUnitIso (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    P ≅ (koszulTensorFunctor T P).obj
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0).obj
        (SheafOfModules.unit (𝓡 T))) :=
  asIso (koszulTensorUnitInclusion T P)

private theorem quotientUnitIso_hom (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    (quotientUnitIso T P).hom = koszulTensorUnitInclusion T P := by
  unfold quotientUnitIso
  rfl

private instance tensorAdditive (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    (koszulTensorFunctor T P).Additive := by
  dsimp only [koszulTensorFunctor]
  infer_instance

private instance tensorColimits (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    PreservesColimitsOfShape WalkingParallelPair (koszulTensorFunctor T P) := by
  let (M : SheafOfModules.{u} (𝓡 T)) :
      PreservesColimitsOfShape WalkingParallelPair
        ((MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T))).flip.obj M) := by
    let : MonoidalClosed (SheafOfModules.{u} (𝓡 T)) := monoidalClosed (R := T)
    let : SymmetricCategory (SheafOfModules.{u} (𝓡 T)) := symmetricCategory T
    change PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorRight M)
    infer_instance
  dsimp only [koszulTensorFunctor]
  infer_instance

@[irreducible] private def unitLeftIso (T : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 T)) :
    ((curriedTensor (SheafOfModules.{u} (𝓡 T))).obj (unit (𝓡 T))).obj M ≅ M :=
  λ_ M

private theorem quotientUnitIso_component (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) (k : ℤ) :
    (quotientUnitIso T P).hom.f k = (unitLeftIso T (P.X k)).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso
        (curriedTensor (SheafOfModules.{u} (𝓡 T))) (unit (𝓡 T)) P k).inv := by
  rw [quotientUnitIso_hom]
  unfold unitLeftIso
  rfl

private theorem monoidal_counit_leftUnitor
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {X : D} {M : E} (e : F.obj X ≅ M)
    (e₀ : F.obj (𝟙_ D) ≅ 𝟙_ E) (h₀ : e₀.inv = Functor.LaxMonoidal.ε F) :
    (e₀.inv ⊗ₘ e.inv) ≫ Functor.LaxMonoidal.μ F (𝟙_ D) X ≫
      F.map (λ_ X).hom ≫ e.hom = (λ_ M).hom := by
  rw [tensorHom_def', Category.assoc, h₀,
    ← Functor.LaxMonoidal.left_unitality_assoc, leftUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

private theorem tensor_leftUnitor_hom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 R)) :
    let := monoidalCategory R
    let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
    let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
    (tensorObjIsoSheafification (unit (𝓡 R)) M).hom ≫
      S.map (λ_ M.val).hom ≫ ε.app M = (unitLeftIso R M).hom := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
  unfold unitLeftIso
  exact monoidal_counit_leftUnitor S ((asIso ε).app M)
    ((asIso ε).app (unit (𝓡 R))) rfl

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] CategoryTheory.Limits.limit

@[irreducible] private def quotientAction (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) : P ⟶ P :=
  (quotientUnitIso T P).hom ≫ (koszulTensorFunctor T P).map
    ((CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0).map
      (endoPow (globalSectionMultiplication T a) (n + 1))) ≫
        (quotientUnitIso T P).inv

private theorem conjugatedCokernelCondition
    {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (G : A ⥤ B) [G.PreservesZeroMorphisms]
    {X : A} (f : X ⟶ X) [HasCokernel f] {Y : B} (e : Y ≅ G.obj X) :
    (e.hom ≫ G.map f ≫ e.inv) ≫ (e.hom ≫ G.map (cokernel.π f)) = 0 := by
  have hz : G.map f ≫ G.map (cokernel.π f) = 0 := by
    rw [← G.map_comp, cokernel.condition, G.map_zero]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hz, comp_zero]

private theorem quotientAction_condition (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) :
    quotientAction T P a n ≫ koszulRepresentativeQuotient T P a n = 0 := by
  let G := CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0 ⋙
    koszulTensorFunctor T P
  let f := endoPow (globalSectionMultiplication T a) (n + 1)
  unfold quotientAction koszulRepresentativeQuotient
  rw [← quotientUnitIso_hom]
  change ((quotientUnitIso T P).hom ≫ G.map f ≫ (quotientUnitIso T P).inv) ≫
    ((quotientUnitIso T P).hom ≫ G.map (cokernel.π f)) = 0
  exact conjugatedCokernelCondition G f (quotientUnitIso T P)

private def transportedCokernel
    {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (G : A ⥤ B) [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair G]
    {X : A} (f : X ⟶ X) [HasCokernel f] {Y : B} (e : Y ≅ G.obj X)
    {g : Y ⟶ Y} (hg : g = e.hom ≫ G.map f ≫ e.inv)
    {q : Y ⟶ G.obj (cokernel f)} (hq : q = e.hom ≫ G.map (cokernel.π f))
    (h : g ≫ q = 0) : IsColimit (CokernelCofork.ofπ q h) := by
  classical
  apply Classical.choice
  constructor
  let hc := isColimitOfHasCokernelOfPreservesColimit G f
  have ht := CokernelCofork.isColimitOfIsColimitOfIff hc g e (by
    intro Z k
    rw [hg, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    constructor
    · intro hk
      rw [hk, comp_zero]
    · intro hk
      apply (cancel_epi e.hom).mp
      simpa only [comp_zero] using hk)
  exact IsColimit.ofIsoColimit ht (Cofork.ext (Iso.refl _) (by simpa using hq.symm))

private def quotientCokernel (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (koszulRepresentativeQuotient T P a n)
      (quotientAction_condition T P a n)) := by
  classical
  apply Classical.choice
  constructor
  let G := CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0 ⋙
    koszulTensorFunctor T P
  let : PreservesColimitsOfShape WalkingParallelPair
      (CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
      (HomologicalComplex.single (SheafOfModules.{u} (𝓡 T)) (.up ℤ) 0))
  have : PreservesColimitsOfShape WalkingParallelPair G := by
    dsimp only [G]
    infer_instance
  let f := endoPow (globalSectionMultiplication T a) (n + 1)
  exact transportedCokernel G f (quotientUnitIso T P)
    (g := quotientAction T P a n) (by unfold quotientAction; rfl)
    (q := koszulRepresentativeQuotient T P a n)
    (by rw [quotientUnitIso_hom]; unfold koszulRepresentativeQuotient; rfl)
    (quotientAction_condition T P a n)

attribute [local irreducible] transportedCokernel quotientCokernel

private theorem singleTensorComponent
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A]
    [Preadditive D] [HasZeroObject D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X : A, (F.obj X).PreservesZeroMorphisms]
    {X : A} (f : X ⟶ X) (P : CochainComplex B ℤ) (k : ℤ) :
    (CochainComplex.mapBifunctorSingle₁XIso F X P k).inv ≫
      (HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P) F (.up ℤ)).f k =
      (F.flip.obj (P.X k)).map f ≫
        (CochainComplex.mapBifunctorSingle₁XIso F X P k).inv := by
  have h := HomologicalComplex.ι_mapBifunctorMap
    ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P) F (.up ℤ)
      0 k k (by simp)
  dsimp only [CochainComplex.mapBifunctorSingle₁XIso]
  simp only [Category.assoc]
  erw [h]
  simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
  let G := F.flip.obj (P.X k)
  have hs : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
      (((HomologicalComplex.single A (.up ℤ) 0).map f).f 0) =
        f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv := by
    rw [HomologicalComplex.single_map_f_self]
    simp
  change G.map _ ≫ G.map _ ≫ _ = G.map _ ≫ G.map _ ≫ _
  exact (G.map_comp_assoc _ _ _).symm.trans
    ((congrArg (fun g ↦ G.map g ≫ _) hs).trans (G.map_comp_assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem unitConjugateComponent
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [(curriedTensor A).PreservesZeroMorphisms]
    [∀ X : A, ((curriedTensor A).obj X).PreservesZeroMorphisms]
    (X : A) (P : CochainComplex A ℤ)
    (l : ∀ k : ℤ, ((curriedTensor A).obj X).obj (P.X k) ≅ P.X k)
    (e : P ≅ HomologicalComplex.mapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj X) P
        (curriedTensor A) (.up ℤ))
    (he : ∀ k, e.hom.f k = (l k).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso (curriedTensor A) X P k).inv)
    (f : X ⟶ X) (k : ℤ) :
    (e.hom ≫ HomologicalComplex.mapBifunctorMap
      ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P)
        (curriedTensor A) (.up ℤ) ≫ e.inv).f k =
      (l k).inv ≫ ((curriedTensor A).flip.obj (P.X k)).map f ≫
        (l k).hom := by
  let b := CochainComplex.mapBifunctorSingle₁XIso (curriedTensor A) X P k
  have hi : (HomologicalComplex.eval A (.up ℤ) k).mapIso e =
      (l k).symm ≪≫ b.symm := Iso.ext (he k)
  have hh := congrArg Iso.hom hi
  have hv := congrArg Iso.inv hi
  simp only [HomologicalComplex.comp_f]
  rw [show e.hom.f k = (l k).inv ≫ b.inv from hh,
    show e.inv.f k = b.hom ≫ (l k).hom from hv]
  have h := singleTensorComponent (curriedTensor A) f P k
  change b.inv ≫ _ = ((curriedTensor A).flip.obj (P.X k)).map f ≫ b.inv at h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun g ↦ (l k).inv ≫ g ≫ b.hom ≫ (l k).hom) h

private theorem quotientAction_component (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) (k : ℤ) :
    (quotientAction T P a n).f k =
      (unitLeftIso T (P.X k)).inv ≫
        ((MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T))).flip.obj
          (P.X k)).map (endoPow (globalSectionMultiplication T a) (n + 1)) ≫
            (unitLeftIso T (P.X k)).hom := by
  unfold quotientAction
  exact unitConjugateComponent (unit (𝓡 T)) P (fun k ↦ unitLeftIso T (P.X k))
    (quotientUnitIso T P) (quotientUnitIso_component T P)
    (endoPow (globalSectionMultiplication T a) (n + 1)) k

attribute [local irreducible] koszulTensorFunctor

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionScalar
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (𝓡 R)).sections) :
    𝟭 (SheafOfModules.{u} (𝓡 R)) ⟶ 𝟭 _ where
  app M :=
    ⟨{ app := fun U => ModuleCat.ofHom
          (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (s.val U))
       naturality := by
         intro U V i
         apply ModuleCat.hom_ext
         apply LinearMap.ext
         intro x
         change (show R.obj.obj V from s.val V) • M.val.map i x =
           M.val.map i ((show R.obj.obj U from s.val U) • x)
         rw [M.val.map_smul]
         exact congrArg (fun a : R.obj.obj V => a • M.val.map i x) (s.property i).symm }⟩
  naturality {M N} a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((a.val.app U).hom.map_smul (s.val U) x).symm

private theorem transportedSquare
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (a : X' ⟶ F.obj X) (b : F.obj Y ⟶ Y')
    (f : X' ⟶ X') (g : X ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Y) (l : Y' ⟶ Y')
    (ha : f ≫ a = a ≫ F.map g) (hpre : g ≫ h = h ≫ k)
    (hb : F.map k ≫ b = b ≫ l) :
    f ≫ (a ≫ F.map h ≫ b) = (a ≫ F.map h ≫ b) ≫ l := by
  rw [← Category.assoc, ha, Category.assoc, ← F.map_comp_assoc,
    hpre, F.map_comp, Category.assoc, hb]
  simp only [Category.assoc]

private theorem scalar_leftUnitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (𝓡 R)).sections)
    (M : SheafOfModules.{u} (𝓡 R)) :
    letI := monoidalCategory R
    globalSectionMultiplication R s ▷ M ≫ (unitLeftIso R M).hom =
      (unitLeftIso R M).hom ≫ (sectionScalar R s).app M := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
  have hpre : (globalSectionMultiplication R s).val ▷ M.val ≫ (λ_ M.val).hom =
      (λ_ M.val).hom ≫ ((sectionScalar R s).app M).val := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    change R.obj.obj V at a
    change (a * (show R.obj.obj V from s.val V)) • x =
      (show R.obj.obj V from s.val V) • (a • x)
    rw [mul_smul, smul_comm]
  have hε := ε.naturality ((sectionScalar R s).app M)
  change S.map ((sectionScalar R s).app M).val ≫ ε.app M =
    ε.app M ≫ (sectionScalar R s).app M at hε
  have h := transportedSquare S
    (tensorObjIsoSheafification (unit (𝓡 R)) M).hom (ε.app M)
    (globalSectionMultiplication R s ▷ M)
    ((globalSectionMultiplication R s).val ▷ M.val) (λ_ M.val).hom
    ((sectionScalar R s).app M).val ((sectionScalar R s).app M)
    (whiskerRight_tensorObjIsoSheafification_hom (R := R)
      (globalSectionMultiplication R s) M) hpre hε
  exact (congrArg (globalSectionMultiplication R s ▷ M ≫ ·)
    (tensor_leftUnitor_hom R M)).symm.trans
      (h.trans (congrArg (· ≫ (sectionScalar R s).app M) (tensor_leftUnitor_hom R M)))

private theorem conjugatedMapPow
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X : A} {Y : B} (e : Y ≅ F.obj X) (f : X ⟶ X) (m : ℕ) :
    e.hom ≫ F.map (endoPow f m) ≫ e.inv =
      endoPow (e.hom ≫ F.map f ≫ e.inv) m := by
  induction m with
  | zero => simp only [endoPow, Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  | succ m ih =>
    simp only [endoPow, Functor.map_comp]
    rw [← ih]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem quotientAction_apply (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) (k : ℤ) (V : Cᵒᵖ)
    (x : (P.X k).val.obj V) :
    ((quotientAction T P a n).f k).val.app V x =
      (show T.obj.obj V from a.val V) ^ (n + 1) • x := by
  let G := (MonoidalCategory.curriedTensor
    (SheafOfModules.{u} (𝓡 T))).flip.obj (P.X k)
  have hbase : (unitLeftIso T (P.X k)).inv ≫ G.map (globalSectionMultiplication T a) ≫
      (unitLeftIso T (P.X k)).hom = (sectionScalar T a).app (P.X k) := by
    exact (congrArg ((unitLeftIso T (P.X k)).inv ≫ ·) (scalar_leftUnitor T a (P.X k))).trans
      (by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp])
  have hp (m : ℕ) :
      ((endoPow ((sectionScalar T a).app (P.X k)) m).val.app V) x =
        (show T.obj.obj V from a.val V) ^ m • x := by
    induction m with
    | zero => change x = _; simp
    | succ m ih =>
      change (show T.obj.obj V from a.val V) •
        ((endoPow ((sectionScalar T a).app (P.X k)) m).val.app V x) = _
      rw [ih, pow_succ, mul_smul, smul_comm]
  rw [quotientAction_component]
  change (( (unitLeftIso T (P.X k)).inv ≫ G.map
    (endoPow (globalSectionMultiplication T a) (n + 1)) ≫
      (unitLeftIso T (P.X k)).hom).val.app V) x = _
  have hpow : (unitLeftIso T (P.X k)).inv ≫ G.map
      (endoPow (globalSectionMultiplication T a) (n + 1)) ≫ (unitLeftIso T (P.X k)).hom =
        endoPow ((sectionScalar T a).app (P.X k)) (n + 1) :=
    (conjugatedMapPow G (unitLeftIso T (P.X k)).symm
      (globalSectionMultiplication T a) (n + 1)).trans
        (congrArg (fun f ↦ endoPow f (n + 1)) hbase)
  exact (congrArg (fun f ↦ (f.val.app V) x) hpow).trans (hp (n + 1))

private instance mapComplexColimits {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasColimitsOfShape WalkingParallelPair A]
    [HasColimitsOfShape WalkingParallelPair B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    PreservesColimitsOfShape WalkingParallelPair (F.mapHomologicalComplex (.up ℤ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro k
  change PreservesColimitsOfShape WalkingParallelPair
    (HomologicalComplex.eval A (.up ℤ) k ⋙ F)
  infer_instance

private theorem restrictionColimits (φ : R ⟶ S) :
    PreservesColimitsOfShape WalkingParallelPair (restrictScalars.{u} (𝓻 φ)) := by
  let U := restrictScalars.{u} (𝓻 φ)
  have h (T : Sheaf J RingCat.{u}) :
      PreservesFiniteColimits (toSheaf.{u} T) :=
    (moduleSheaves_colimits_forgetful.{u, u, u, u} T).2.2.1
  have := h (𝓡 R)
  have := h (𝓡 S)
  have : ReflectsColimitsOfShape WalkingParallelPair (toSheaf.{u} (𝓡 R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape WalkingParallelPair (U ⋙ toSheaf (𝓡 R)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (toSheaf.{u} (𝓡 S)))
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (J := WalkingParallelPair) U (toSheaf.{u} (𝓡 R))

private def quotientAugmentation (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (unit (𝓡 T)).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ reductionTensorTower T P a :=
  koszulStrictAugmentation T P a ≫ koszulTensorTowerComparison T P a

private theorem quotientTowerMap_app (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) :
    (quotientAugmentation T P a).app (op n) =
      koszulRepresentativeQuotient T P a n :=
  koszulRepresentativeAugmentation_quotient T P a n

attribute [local irreducible] reductionTensorTower
  koszulRepresentativeQuotient

private theorem finitePowerMap_square
    {A : Type*} [Category* A] [HasFiniteProducts A] (d : ℕ)
    {P Q : A} (f : P ⟶ P) (g : Q ⟶ Q) (α : P ⟶ ∏ᶜ fun _ : Fin d ↦ Q)
    (h : ∀ i : Fin d, f ≫ α ≫ Pi.π (fun _ : Fin d ↦ Q) i =
      α ≫ Pi.π (fun _ : Fin d ↦ Q) i ≫ g) :
    f ≫ α = α ≫ Limits.Pi.map (fun _ : Fin d ↦ g) := by
  apply Pi.hom_ext
  intro i
  simpa only [Category.assoc, Pi.map_π] using h i

private theorem quotientAction_square (φ : R ⟶ S) (d : ℕ)
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ)
    (Q : CochainComplex (SheafOfModules.{u} (𝓡 S)) ℤ)
    (α : ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
        Q ⟶ ∏ᶜ fun _ : Fin d ↦ P)
    (a : (unit (𝓡 R)).sections) (n : ℕ) :
    ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).map
        (quotientAction S Q
          ((Functor.sectionsFunctor Cᵒᵖ).map
            (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a) n) ≫ α =
      α ≫ Limits.Pi.map (fun _ : Fin d ↦ quotientAction R P a n) := by
  refine finitePowerMap_square d _ (quotientAction R P a n) α ?_
  intro i
  apply HomologicalComplex.Hom.ext
  funext k
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let f := ((α ≫ Pi.π (fun _ : Fin d ↦ P) i).f k).val.app V
  have hS := quotientAction_apply S Q
    ((Functor.sectionsFunctor Cᵒᵖ).map
      (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a) n k V x
  have hR := quotientAction_apply R P a n k V (f x)
  have hl := f.hom.map_smul ((show R.obj.obj V from a.val V) ^ (n + 1)) x
  let xS : (Q.X k).val.obj V := x
  have hx : (show S.obj.obj V from
      (((Functor.sectionsFunctor Cᵒᵖ).map
        (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a).val V)) ^ (n + 1) • xS =
      (show R.obj.obj V from a.val V) ^ (n + 1) • x := by
    change ((φ.hom.app V).hom (show R.obj.obj V from a.val V)) ^ (n + 1) • xS = _
    rw [← map_pow]
    rfl
  change f _ = _
  exact (congrArg f hS).trans ((congrArg f hx).trans (hl.trans hR.symm))

@[irreducible] private def compatibleCokernelIso
    {A : Type*} [Category* A] [HasZeroMorphisms A]
    {X X' : A} {f : X ⟶ X} {g : X' ⟶ X'}
    {c : CokernelCofork f} {c' : CokernelCofork g}
    (hc : IsColimit c) (hc' : IsColimit c') (α : X ≅ X')
    (hα : f ≫ α.hom = α.hom ≫ g) :
    { β : c.pt ≅ c'.pt // c.π ≫ β.hom = α.hom ≫ c'.π } := by
  classical
  apply Classical.choice
  constructor
  refine ⟨CokernelCofork.mapIsoOfIsColimit hc hc' (Arrow.isoMk α α hα.symm), ?_⟩
  exact CokernelCofork.π_mapOfIsColimit hc _ _

@[irreducible] private def mappedCokernelComparison
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (F : A ⥤ D) (G : B ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F]
    [PreservesColimitsOfShape WalkingParallelPair G]
    {X : A} {Y : B} {f : X ⟶ X} {g : Y ⟶ Y}
    (c : CokernelCofork f) (c' : CokernelCofork g)
    (hc : IsColimit c) (hc' : IsColimit c') (α : F.obj X ≅ G.obj Y)
    (hα : F.map f ≫ α.hom = α.hom ≫ G.map g) :
    { β : F.obj c.pt ≅ G.obj c'.pt // F.map c.π ≫ β.hom = α.hom ≫ G.map c'.π } :=
  compatibleCokernelIso (CokernelCofork.mapIsColimit c hc F)
    (CokernelCofork.mapIsColimit c' hc' G) α hα

@[irreducible] private def quotientLevelData (φ : R ⟶ S) (d : ℕ)
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ)
    (Q : CochainComplex (SheafOfModules.{u} (𝓡 S)) ℤ)
    (α : ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
        Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
    (a : (unit (𝓡 R)).sections) (n : ℕ) :
    { β : ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
      ((reductionTensorTower S Q
        ((Functor.sectionsFunctor Cᵒᵖ).map
          (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a)).obj (op n)) ≅
      ∏ᶜ fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n) //
      ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).map
        (koszulRepresentativeQuotient S Q
          ((Functor.sectionsFunctor Cᵒᵖ).map
            (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a) n) ≫ β.hom =
        α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n) } := by
  classical
  apply Classical.choice
  constructor
  let U := restrictScalars.{u} (𝓻 φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let FC := finitePowerFunctor (A := CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ) d
  let aS : (unit (𝓡 S)).sections := (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a
  have : PreservesColimitsOfShape WalkingParallelPair U := restrictionColimits φ
  have hα : UC.map (quotientAction S Q aS n) ≫ α.hom =
      α.hom ≫ FC.map (quotientAction R P a n) :=
    quotientAction_square φ d P Q α.hom a n
  exact mappedCokernelComparison UC FC
    (CokernelCofork.ofπ (koszulRepresentativeQuotient S Q aS n)
      (quotientAction_condition S Q aS n))
    (CokernelCofork.ofπ (koszulRepresentativeQuotient R P a n)
      (quotientAction_condition R P a n))
    (quotientCokernel S Q aS n) (quotientCokernel R P a n) α hα

private theorem quotientTowerNaturality (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (unit (𝓡 T)).sections) {n m : ℕᵒᵖ} (f : n ⟶ m) :
    koszulRepresentativeQuotient T P a n.unop ≫ (reductionTensorTower T P a).map f =
      koszulRepresentativeQuotient T P a m.unop := by
  have hn : (quotientAugmentation T P a).app n =
      koszulRepresentativeQuotient T P a n.unop := quotientTowerMap_app T P a n.unop
  have hm : (quotientAugmentation T P a).app m =
      koszulRepresentativeQuotient T P a m.unop := quotientTowerMap_app T P a m.unop
  rw [← hn, ← hm]
  have h := (quotientAugmentation T P a).naturality f
  change 𝟙 P ≫ (quotientAugmentation T P a).app m =
    (quotientAugmentation T P a).app n ≫ (reductionTensorTower T P a).map f at h
  exact h.symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
@[irreducible] private def towerPowerIso {A : Type*} [Category* A] [HasFiniteProducts A]
    (d : ℕ) (Y : ℕᵒᵖ ⥤ A) :
    Y ⋙ finitePowerFunctor d ≅ ∏ᶜ fun _ : Fin d ↦ Y := by
  let t : Y ⋙ finitePowerFunctor d ⟶ ∏ᶜ fun _ : Fin d ↦ Y :=
    Pi.lift (fun i ↦ { app := fun n ↦ Pi.π (fun _ : Fin d ↦ Y.obj n) i
                       naturality := by
                         intro n m f
                         exact Pi.map_π (fun _ : Fin d ↦ Y.map f) i })
  have (n : ℕᵒᵖ) : IsIso (t.app n) := by
    let E := (evaluation ℕᵒᵖ A).obj n
    have ht : t.app n ≫ piComparison E (fun _ : Fin d ↦ Y) = 𝟙 _ := by
      apply Pi.hom_ext
      intro i
      rw [Category.assoc, piComparison_comp_π]
      change ((t ≫ Pi.π (fun _ : Fin d ↦ Y) i).app n) = _
      rw [Pi.lift_π, Category.id_comp]
      rfl
    have : IsIso (t.app n ≫ piComparison E (fun _ : Fin d ↦ Y)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (piComparison E (fun _ : Fin d ↦ Y))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private theorem towerPowerIso_projection {A : Type*} [Category* A] [HasFiniteProducts A]
    (d : ℕ) (Y : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) (i : Fin d) :
    ((towerPowerIso d Y).hom ≫ Pi.π (fun _ : Fin d ↦ Y) i).app n =
      Pi.π (fun _ : Fin d ↦ Y.obj n) i := by
  unfold towerPowerIso
  simp only [asIso_hom, Pi.lift_π]

private theorem quotientMap_epi (φ : R ⟶ S)
    (P : CochainComplex (SheafOfModules.{u} (𝓡 S)) ℤ)
    (a : (unit (𝓡 S)).sections) (n : ℕ) :
    Epi (((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).map
      (koszulRepresentativeQuotient S P a n)) := by
  have : PreservesColimitsOfShape WalkingParallelPair (restrictScalars.{u} (𝓻 φ)) :=
    restrictionColimits φ
  exact Cofork.IsColimit.epi
    (CokernelCofork.mapIsColimit _ (quotientCokernel S P a n)
      ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)))

@[irreducible] private def towerIsoOfQuotientSquares
    {A : Type*} [Category* A] {X Y : ℕᵒᵖ ⥤ A} {P Q : A}
    (qX : ∀ n, P ⟶ X.obj n) (qY : ∀ n, Q ⟶ Y.obj n) (α : P ≅ Q)
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (hX : ∀ {n m} (f : n ⟶ m), qX n ≫ X.map f = qX m)
    (hY : ∀ {n m} (f : n ⟶ m), qY n ≫ Y.map f = qY m)
    (he : ∀ n, qX n ≫ (e n).hom = α.hom ≫ qY n)
    (hq : ∀ n, Epi (qX n)) : X ≅ Y :=
  NatIso.ofComponents e (by
    intro n m f
    have := hq n
    apply (cancel_epi (qX n)).mp
    calc
      qX n ≫ X.map f ≫ (e m).hom = qX m ≫ (e m).hom := by
        rw [← Category.assoc, hX]
      _ = α.hom ≫ qY m := he m
      _ = α.hom ≫ qY n ≫ Y.map f := by rw [hY]
      _ = (α.hom ≫ qY n) ≫ Y.map f := (Category.assoc _ _ _).symm
      _ = (qX n ≫ (e n).hom) ≫ Y.map f :=
        congrArg (fun t ↦ t ≫ Y.map f) (he n).symm
      _ = qX n ≫ (e n).hom ≫ Y.map f := Category.assoc _ _ _)

private theorem towerIsoOfQuotientSquares_hom_app
    {A : Type*} [Category* A] {X Y : ℕᵒᵖ ⥤ A} {P Q : A}
    (qX : ∀ n, P ⟶ X.obj n) (qY : ∀ n, Q ⟶ Y.obj n) (α : P ≅ Q)
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (hX : ∀ {n m} (f : n ⟶ m), qX n ≫ X.map f = qX m)
    (hY : ∀ {n m} (f : n ⟶ m), qY n ≫ Y.map f = qY m)
    (he : ∀ n, qX n ≫ (e n).hom = α.hom ≫ qY n)
    (hq : ∀ n, Epi (qX n)) (n : ℕᵒᵖ) :
    (towerIsoOfQuotientSquares qX qY α e hX hY he hq).hom.app n = (e n).hom := by
  unfold towerIsoOfQuotientSquares
  rfl

@[irreducible] private def towerPowerIsoOfQuotientSquares
    {A : Type*} [Category* A] [HasFiniteProducts A]
    (d : ℕ) (Y : ℕᵒᵖ ⥤ A) {X : ℕᵒᵖ ⥤ A} {P Q : A}
    (qX : ∀ n, P ⟶ X.obj n)
    (qY : ∀ n, Q ⟶ (Y ⋙ finitePowerFunctor d).obj n) (α : P ≅ Q)
    (e : ∀ n, X.obj n ≅ (Y ⋙ finitePowerFunctor d).obj n)
    (hX : ∀ {n m} (f : n ⟶ m), qX n ≫ X.map f = qX m)
    (hY : ∀ {n m} (f : n ⟶ m),
      qY n ≫ (Y ⋙ finitePowerFunctor d).map f = qY m)
    (he : ∀ n, qX n ≫ (e n).hom = α.hom ≫ qY n)
    (hq : ∀ n, Epi (qX n)) :
    { σ : X ≅ ∏ᶜ fun _ : Fin d ↦ Y // ∀ (n : ℕᵒᵖ) (i : Fin d),
      (σ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i).app n =
        (e n).hom ≫ Pi.π (fun _ : Fin d ↦ Y.obj n) i } := by
  classical
  apply Classical.choice
  constructor
  let δ := towerIsoOfQuotientSquares qX qY α e hX hY he hq
  refine ⟨δ ≪≫ towerPowerIso d Y, ?_⟩
  intro n i
  simp only [Iso.trans_hom, Category.assoc, NatTrans.comp_app]
  have hd : δ.hom.app n = (e n).hom :=
    towerIsoOfQuotientSquares_hom_app qX qY α e hX hY he hq n
  rw [hd]
  have h := towerPowerIso_projection d Y n i
  simp only [NatTrans.comp_app] at h
  exact congrArg ((e n).hom ≫ ·) h

@[irreducible] private def quotientStrictData (φ : R ⟶ S) (d : ℕ)
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ)
    (Q : CochainComplex (SheafOfModules.{u} (𝓡 S)) ℤ)
    (α : ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
        Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
    (a : (unit (𝓡 R)).sections) :
    { σ : reductionTensorTower S Q
      ((Functor.sectionsFunctor Cᵒᵖ).map
        (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a) ⋙
      (restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ) ≅
        ∏ᶜ fun _ : Fin d ↦ reductionTensorTower R P a // ∀ (n : ℕ) (i : Fin d),
      (σ.hom ≫ Pi.π (fun _ : Fin d ↦ reductionTensorTower R P a) i).app (op n) =
        ((quotientLevelData φ d P Q α a n).val).hom ≫
          Pi.π (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i } := by
  classical
  apply Classical.choice
  constructor
  let U := restrictScalars.{u} (𝓻 φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let aS : (unit (𝓡 S)).sections := (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a
  let Y := reductionTensorTower R P a
  let F := finitePowerFunctor (A := CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ) d
  let δ := towerPowerIsoOfQuotientSquares d Y
    (X := reductionTensorTower S Q aS ⋙ UC) (P := UC.obj Q) (Q := F.obj P)
      (fun n ↦ UC.map (koszulRepresentativeQuotient S Q aS n.unop))
      (fun n ↦ F.map (koszulRepresentativeQuotient R P a n.unop)) α
      (fun n ↦ (quotientLevelData φ d P Q α a n.unop).val)
      (fun f ↦ (UC.map_comp _ _).symm.trans
        (congrArg UC.map (quotientTowerNaturality S Q aS f)))
      (fun f ↦ (F.map_comp _ _).symm.trans
        (congrArg F.map (quotientTowerNaturality R P a f)))
      (fun n ↦ (quotientLevelData φ d P Q α a n.unop).property)
      (fun n ↦ quotientMap_epi φ Q aS n.unop)
  exact ⟨δ.val, fun n i ↦ δ.property (op n) i⟩


private theorem powerIso_projection
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B) (d : ℕ)
    {X Y : A} [HasProduct (fun _ : Fin d ↦ Y)]
    [HasProduct (fun _ : Fin d ↦ F.obj Y)]
    [PreservesLimit (Discrete.functor (fun _ : Fin d ↦ Y)) F]
    (e : X ≅ ∏ᶜ fun _ : Fin d ↦ Y) (i : Fin d) :
    (F.mapIso e ≪≫ PreservesProduct.iso F (fun _ : Fin d ↦ Y)).hom ≫
        Pi.π (fun _ : Fin d ↦ F.obj Y) i =
      F.map (e.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
    Category.assoc, piComparison_comp_π, ← F.map_comp]

private theorem twicePowerIso_projection
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (F : A ⥤ B) (G : B ⥤ D) (d : ℕ) {X Y : A}
    [HasProduct (fun _ : Fin d ↦ Y)]
    [HasProduct (fun _ : Fin d ↦ F.obj Y)]
    [HasProduct (fun _ : Fin d ↦ G.obj (F.obj Y))]
    [PreservesLimit (Discrete.functor (fun _ : Fin d ↦ Y)) F]
    [PreservesLimit (Discrete.functor (fun _ : Fin d ↦ F.obj Y)) G]
    (e : X ≅ ∏ᶜ fun _ : Fin d ↦ Y) (i : Fin d) :
    let eF := F.mapIso e ≪≫ PreservesProduct.iso F (fun _ : Fin d ↦ Y)
    (G.mapIso eF ≪≫ PreservesProduct.iso G (fun _ : Fin d ↦ F.obj Y)).hom ≫
        Pi.π (fun _ : Fin d ↦ G.obj (F.obj Y)) i =
      G.map (F.map (e.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i)) := by
  exact (powerIso_projection G d
    (F.mapIso e ≪≫ PreservesProduct.iso F (fun _ : Fin d ↦ Y)) i).trans
    (congrArg G.map (powerIso_projection F d e i))

private def transposeTowerFunctor
    {A : Type*} [Category* A] [HasZeroMorphisms A] :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  obj X :=
    { X := fun i ↦
        { obj := fun n ↦ (X.obj n).X i
          map := fun f ↦ (X.map f).f i
          map_id := fun n ↦ by simp
          map_comp := fun f g ↦ by simp }
      d := fun i j ↦ { app := fun n ↦ (X.obj n).d i j }
      shape := fun i j h ↦ NatTrans.ext (by funext n; exact (X.obj n).shape i j h)
      d_comp_d' := fun i j k _ _ ↦
        NatTrans.ext (by funext n; exact (X.obj n).d_comp_d i j k) }
  map f :=
    { f := fun i ↦
        { app := fun n ↦ (f.app n).f i
          naturality := fun n m g ↦ congrArg (fun h ↦ h.f i) (f.naturality g) }
      comm' := fun i j _ ↦ NatTrans.ext (by funext n; exact (f.app n).comm i j) }
  map_id := by intro X; ext k n; rfl
  map_comp := by intro X Y Z f g; ext k n; rfl

private instance transposeProducts
    {A : Type*} [Category* A] [HasZeroMorphisms A] [HasFiniteProducts A] (d : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin d)) (transposeTowerFunctor (A := A)) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro k
  apply preservesLimitsOfShape_of_evaluation
  intro n
  change PreservesLimitsOfShape (Discrete (Fin d))
    ((evaluation ℕᵒᵖ (CochainComplex A ℤ)).obj n ⋙
      HomologicalComplex.eval _ (.up ℤ) k)
  infer_instance

private instance whiskerPreservesZero
    {I A B : Type*} [Category* I] [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] :
    ((Functor.whiskeringRight I A B).obj F).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i
    exact F.map_zero (X.obj i) (Y.obj i)

@[irreducible] private def transposedPowerIso
    {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasFiniteProducts B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] (d : ℕ)
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) (Y : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (e : X ⋙ F.mapHomologicalComplex (.up ℤ) ≅ ∏ᶜ fun _ : Fin d ↦ Y) :
    ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj
      (transposeTowerFunctor.obj X)) ≅
        ∏ᶜ fun _ : Fin d ↦ transposeTowerFunctor.obj Y :=
  transposeTowerFunctor.mapIso e ≪≫ PreservesProduct.iso transposeTowerFunctor
    (fun _ : Fin d ↦ Y)

private theorem transposedPowerIso_projection
    {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasFiniteProducts B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] (d : ℕ)
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) (Y : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (e : X ⋙ F.mapHomologicalComplex (.up ℤ) ≅ ∏ᶜ fun _ : Fin d ↦ Y)
    (n : ℕ) (i : Fin d) :
    let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)
    (E.mapIso (transposedPowerIso F d X Y e) ≪≫ PreservesProduct.iso E
      (fun _ : Fin d ↦ transposeTowerFunctor.obj Y)).hom ≫
        Pi.π (fun _ : Fin d ↦ Y.obj (op n)) i =
      (e.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i).app (op n) := by
  let T := transposeTowerFunctor (A := B)
  let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)
  unfold transposedPowerIso
  exact twicePowerIso_projection T E d e i

/-- A scalar-coordinate isomorphism induces an isomorphism of the full strict
quotient system, compatibly with every quotient augmentation.

Source: Stacks Project, sites-modules.tex, Tags 03DA, 03DB and Section 03EK;
Bhatt--Scholze, Lemma 3.4.12, finite direct-sum calculation.
(blueprint: lem-pur-finite-free-quotient-tower)

Proof: Fix the given R-linear chain isomorphism alpha. For each
n the quotient tensor is the cokernel of multiplication by a^(n+1), because tensor
preserves cokernels. This assertion concerns sheaf cokernels: sections of a quotient
lift only locally, which suffices by the sheafification universal property.
Restriction of scalars preserves cokernels, and alpha intertwines multiplication by
a^(n+1). Its induced cokernel isomorphism therefore identifies the quotient level
with the finite power of the R quotient level. It has the displayed quotient square.
The quotient augmentation is epic. Precomposing the transition square by it reduces
the square to naturality of the two quotient augmentations, hence the level
isomorphisms form a strict tower isomorphism. Transposing towers and taking the
canonical finite product comparison gives tau. For rank zero, alpha identifies the
restricted extension with the empty product; its quotient cokernels are also zero,
as are the empty powers of the R quotient levels. No regularity, flatness or exact infinite products
are used. -/
theorem finiteFreeQuotientTower (φ : R ⟶ S) (d : ℕ)
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ)
    (Q : CochainComplex (SheafOfModules.{u} (𝓡 S)) ℤ)
    (α : ((restrictScalars.{u} (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
        Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
    (a : (unit (𝓡 R)).sections) :
    let U := restrictScalars.{u} (𝓻 φ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let aS := (Functor.sectionsFunctor Cᵒᵖ).map
      (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a
    let X := koszulTowerComplex S (reductionTensorTower S Q aS)
    let Y := koszulTowerComplex R (reductionTensorTower R P a)
    ∃ τ : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj U).mapHomologicalComplex
        (.up ℤ)).obj X) ≅ ∏ᶜ fun _ : Fin d ↦ Y,
      ∀ n : ℕ,
        let E := ((evaluation ℕᵒᵖ (SheafOfModules.{u} (𝓡 R))).obj (op n)).mapHomologicalComplex
          (.up ℤ)
        let θ := E.mapIso τ ≪≫ PreservesProduct.iso E (fun _ : Fin d ↦ Y)
        UC.map (koszulRepresentativeQuotient S Q aS n) ≫ θ.hom =
          α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n) := by
  classical
  let U := restrictScalars.{u} (𝓻 φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let aS : (unit (𝓡 S)).sections := (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a
  let Y := reductionTensorTower R P a
  let σ := quotientStrictData φ d P Q α a
  let τ := transposedPowerIso U d (reductionTensorTower S Q aS) Y σ.val
  refine ⟨τ, ?_⟩
  intro n
  let E := ((evaluation ℕᵒᵖ (SheafOfModules.{u} (𝓡 R))).obj
    (op n)).mapHomologicalComplex (.up ℤ)
  let θ := E.mapIso τ ≪≫ PreservesProduct.iso E
    (fun _ : Fin d ↦ koszulTowerComplex R Y)
  have hθ : θ.hom = ((quotientLevelData φ d P Q α a n).val).hom := by
    apply Pi.hom_ext
    intro i
    exact (transposedPowerIso_projection U d (reductionTensorTower S Q aS) Y
      σ.val n i).trans (σ.property n i)
  exact (congrArg (UC.map (koszulRepresentativeQuotient S Q aS n) ≫ ·) hθ).trans
    (quotientLevelData φ d P Q α a n).property

end CategoryTheory
