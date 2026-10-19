/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
/-!
# Invariance of augmented scalar-extension Roos complexes

Source: Stacks Project, Tags 06YS, 06YT, 06YY and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
The tower is indexed by n in N, corresponding to positive level n+1. Its algebra
structure is the natural transformation from the constant ring sheaf R. All tensor
objects use the recorded site tensor. The Roos complex has precisely the coordinates
V^i plus V^(i-1), differential (dx, (1-s)x-dy), and augmentation (p tensor 1, 0).
The helper existence statements uniquely determine maps on every section; no object
is selected from an unnormalized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.KFlatRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

/-- The existing module category of the underlying ring sheaf.
Source: Stacks Tag 03DA (blueprint: lem-pe-kflat-roos-representative-invariance). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- An R-algebra sheaf as an R-module, by the existing restriction of scalars.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModule {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) : Modules R :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map ι)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

-- Retain the existing instance binders in the public API.
set_option linter.unusedSectionVars false in
/-- The algebra map has a unique R-linear sheaf map with its original section values.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the equation on structure maps makes the sectionwise ring homomorphism
R-linear. Ring-map naturality makes these linear maps a sheaf morphism. Conversely,
the displayed value on every section determines every component, hence the map. -/
theorem algebraModuleMap_existsUnique {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :
    ∃! a : algebraModule ι ⟶ algebraModule ι',
      ∀ (U : Cᵒᵖ) (b : B.obj.obj U), a.val.app U b = f.hom.app U b := by
  let a : algebraModule ι ⟶ algebraModule ι' :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (algebraModule ι).val.obj U) (Y := (algebraModule ι').val.obj U)
        { toFun := f.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r b
            change B.obj.obj U at b
            change R.obj.obj U at r
            change f.hom.app U (ι.hom.app U r * b) =
              ι'.hom.app U r * f.hom.app U b
            rw [map_mul]
            have hh := congrArg (fun g : R ⟶ B' ↦ g.hom.app U r) h
            exact congrArg (fun z ↦ z * f.hom.app U b) hh }
       naturality := by
         intro U V g
         ext b
         exact ConcreteCategory.congr_hom (f.hom.naturality g) b }⟩
  refine ⟨a, fun _ _ ↦ rfl, ?_⟩
  intro a' ha'
  ext U b
  exact ha' U b

/-- The uniquely normalized map of underlying algebra modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModuleMap {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :=
  (algebraModuleMap_existsUnique ι ι' f h).exists.choose

set_option linter.unusedSectionVars false in
/-- The unit of scalar extension, uniquely specified on all local sections.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: p to p tensor 1 is additive, R-linear and commutes with restrictions;
compose with the module-sheafification unit. It is natural in the input module.
Every component is determined on every section, so this transformation is unique. -/
theorem tensorUnit_existsUnique {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :
    ∃! η : 𝟭 (Modules R) ⟶ siteSheafTensorRight (algebraModule ι),
      ∀ (M : Modules R) (U : Cᵒᵖ) (p : M.val.obj U),
        (η.app M).val.app U p = siteSheafTensorTmul M (algebraModule ι) U p (1 : B.obj.obj U) := by
  let q (M : Modules R) : M.val ⟶ siteTensorPresheaf M.val (algebraModule ι).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U)
        (Y := (siteTensorPresheaf M.val (algebraModule ι).val).obj U)
        ((TensorProduct.mk (R.obj.obj U) (M.val.obj U)
          ((algebraModule ι).val.obj U)).flip (1 : B.obj.obj U))
      naturality := by
        intro U V g
        ext p
        change M.val.map g p ⊗ₜ[R.obj.obj V]
            (show (algebraModule ι).val.obj V from (1 : B.obj.obj V)) =
          M.val.map g p ⊗ₜ[R.obj.obj V]
            ((algebraModule ι).val.map g (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)))
        have h_one : (algebraModule ι).val.map g
            (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)) =
              (show (algebraModule ι).val.obj V from (1 : B.obj.obj V)) :=
          map_one (B.obj.map g).hom
        rw [h_one] }
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let η : 𝟭 (Modules R) ⟶ siteSheafTensorRight (algebraModule ι) :=
    { app := fun M ↦ ⟨q M ≫ adj.unit.app _⟩
      naturality := by
        intro M N f
        apply SheafOfModules.hom_ext
        change f.val ≫ (q N ≫ adj.unit.app _) =
          (q M ≫ adj.unit.app _) ≫
            ((PresheafOfModules.sheafification
              (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
              (𝟙 _)).map (siteTensorHom f.val (algebraModule ι).val)).val
        ext U p
        have hf := adj.unit.naturality (siteTensorHom f.val (algebraModule ι).val)
        have hf' := congrArg (fun g ↦ (g.app U) (p ⊗ₜ[R.obj.obj U]
          (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)))) hf
        exact hf' }
  refine ⟨η, fun _ _ _ ↦ rfl, ?_⟩
  intro η' hη'
  ext M U p
  exact hη' M U p


/-- The actual scalar-extension unit, with the prescribed pure-tensor formula.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def tensorUnit {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :=
  (tensorUnit_existsUnique ι).exists.choose

set_option linter.unusedSectionVars false in
private theorem tensorSecondMap_tmul
    (M N N' : Modules R) (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (siteSheafTensorSecondMap M g).val.app U (siteSheafTensorTmul M N U x y) =
      siteSheafTensorTmul M N' U x (g.val.app U y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h := adj.unit.naturality (siteTensorSecondMap M.val g.val)
  exact (congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] y)) h).symm

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
  (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B)

/-- The module sheaf B_n with its given R-action.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelModule (n : ℕ) : Modules R := algebraModule (ι.app (op n))

set_option linter.unusedSectionVars false in
/-- Compatibility of the algebra structure with the consecutive transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: naturality of ι at n+1 to n, followed by the identity law for the constant functor. -/
theorem structure_compatible (n : ℕ) :
    ι.app (op (n + 1)) ≫ B.map (homOfLE (Nat.le_succ n)).op = ι.app (op n) := by
  simpa using (ι.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The given transition, regarded as an R-module sheaf map.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelMap (n : ℕ) : levelModule B ι (n + 1) ⟶ levelModule B ι n :=
  algebraModuleMap (ι.app (op (n + 1))) (ι.app (op n))
    (B.map (homOfLE (Nat.le_succ n)).op) (structure_compatible B ι n)

/-- Termwise scalar extension, restricted back to R-modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def level (n : ℕ) : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (siteSheafTensorRight (levelModule B ι n)).mapHomologicalComplex (.up ℤ)

/-- Strict tensor transition induced by the algebra transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def transition (P : CochainComplex (Modules R) ℤ) (n : ℕ) :
    (level B ι (n + 1)).obj P ⟶ (level B ι n).obj P :=
  (NatTrans.mapHomologicalComplex (siteSheafTensorRightMap (levelMap B ι n)) (.up ℤ)).app P

private theorem tensorUnit_levelMap (n : ℕ) :
    tensorUnit (ι.app (op (n + 1))) ≫ siteSheafTensorRightMap (levelMap B ι n) =
      tensorUnit (ι.app (op n)) := by
  ext M U p
  change (siteSheafTensorSecondMap M (levelMap B ι n)).val.app U
      ((tensorUnit (ι.app (op (n + 1)))).app M |>.val.app U p) =
    ((tensorUnit (ι.app (op n))).app M).val.app U p
  dsimp only [tensorUnit, levelModule]
  rw [(tensorUnit_existsUnique (ι.app (op (n + 1)))).exists.choose_spec,
    (tensorUnit_existsUnique (ι.app (op n))).exists.choose_spec,
    tensorSecondMap_tmul]
  have hm := (algebraModuleMap_existsUnique
    (ι.app (op (n + 1))) (ι.app (op n))
    (B.map (homOfLE (Nat.le_succ n)).op) (structure_compatible B ι n)).exists.choose_spec
  change siteSheafTensorTmul M (levelModule B ι n) U p
      ((levelMap B ι n).val.app U (1 : (B.obj (op (n + 1))).obj.obj U)) = _
  congr 1
  exact (hm U (1 : (B.obj (op (n + 1))).obj.obj U)).trans
    (map_one ((B.map (homOfLE (Nat.le_succ n)).op).hom.app U).hom)

variable [HasCountableProducts (Modules R)]

/-- The termwise product V(P) of the scalar-extension tower.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def product (P : CochainComplex (Modules R) ℤ) :=
  ∏ᶜ fun n : ℕ => (level B ι n).obj P

/-- The endomorphism 1-s, whose nth coordinate is pr_n minus t_n pr_(n+1).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def oneSubShift (P : CochainComplex (Modules R) ℤ) : product B ι P ⟶ product B ι P :=
  Pi.lift (fun n => Pi.π (fun k : ℕ => (level B ι k).obj P) n -
    Pi.π (fun k : ℕ => (level B ι k).obj P) (n + 1) ≫ transition B ι P n)

/-- The two coordinates of L(P) in degree i, in the order used in the node.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosX (P : CochainComplex (Modules R) ℤ) (i : ℤ) :=
  (product B ι P).X i ⊞ (product B ι P).X (i - 1)

/-- The differential (x,y) to (dx,(1-s)x-dy).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosD (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosX B ι P i ⟶ roosX B ι P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product B ι P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift B ι P).f i ≫
      eqToHom (congrArg (product B ι P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product B ι P).d (i - 1) ((i + 1) - 1))

set_option linter.unusedSectionVars false in
/-- The displayed Roos differential squares to zero.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the first coordinate is d squared, hence zero. The second is
(1-s)dx-d(1-s)x+d squared y; 1-s is a chain map, so these terms cancel. -/
theorem roosD_sq (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosD B ι P i ≫ roosD B ι P (i + 1) = 0 := by
  apply biprod.hom_ext
  · simp [roosD, Category.assoc]
  · simp +instances only [roosX, roosD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.lift_fst_assoc,
      eqToHom_naturality_assoc, eqToHom_refl, Category.id_comp, biprod.lift_snd_assoc,
      Preadditive.sub_comp, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d,
      comp_zero, sub_zero, zero_comp]
    apply sub_eq_zero.mpr
    have hd := eqToHom_naturality
      (fun j : ℤ ↦ (product B ι P).d j (i + 1 + 1 - 1))
      (Int.add_sub_cancel i 1).symm
    simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
      congrArg (fun f ↦ biprod.fst ≫ f ≫
        (oneSubShift B ι P).f (i + 1 + 1 - 1)) hd

/-- The specified Roos complex, with real objects and differential.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roos (P : CochainComplex (Modules R) ℤ) : CochainComplex (Modules R) ℤ :=
  CochainComplex.of (roosX B ι P) (roosD B ι P) (roosD_sq B ι P)

/-- The product of the tensor units in degree i.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def unitProduct (P : CochainComplex (Modules R) ℤ) : P ⟶ product B ι P :=
  Pi.lift (fun n =>
    (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op n))) (.up ℤ)).app P)

set_option linter.unusedSectionVars false in
private theorem unitProduct_oneSubShift (P : CochainComplex (Modules R) ℤ) :
    unitProduct B ι P ≫ oneSubShift B ι P = 0 := by
  apply Pi.hom_ext
  intro n
  have hunit :
      (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op (n + 1)))) (.up ℤ)).app P ≫
          transition B ι P n =
        (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op n))) (.up ℤ)).app P := by
    ext j : 1
    exact congrArg (fun η ↦ η.app (P.X j)) (tensorUnit_levelMap B ι n)
  simp [unitProduct, oneSubShift, Category.assoc, Preadditive.comp_sub, hunit]

/-- The augmentation (unit,0) commutes with differentials.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor units commute with d. The algebra transitions preserve 1, so
(1-s) composed with the product unit is zero, giving the second coordinate. -/
theorem augmentation_comm (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    biprod.lift ((unitProduct B ι P).f i) 0 ≫ (roos B ι P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct B ι P).f (i + 1)) 0 := by
  have hunit (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j)
    (unitProduct_oneSubShift B ι P)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hunit
  simp only [roos, CochainComplex.of_d]
  apply biprod.hom_ext
  · simp [roosD, Category.assoc]
  · simp [roosD, Category.assoc, hunit]

/-- The actual augmentation p to ((p tensor 1)_n,0).
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def augmentation (P : CochainComplex (Modules R) ℤ) : P ⟶ roos B ι P :=
  CochainComplex.ofHom (fun i => biprod.lift ((unitProduct B ι P).f i) 0)
    (augmentation_comm B ι P)

/-- The product of a tensor B_n over all levels.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def productMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    product B ι P ⟶ product B ι P' :=
  Limits.Pi.map (fun n => (level B ι n).map a)

set_option linter.unusedSectionVars false in
private theorem productMap_oneSubShift {P P' : CochainComplex (Modules R) ℤ}
    (a : P ⟶ P') :
    productMap B ι a ≫ oneSubShift B ι P' =
      oneSubShift B ι P ≫ productMap B ι a := by
  apply Pi.hom_ext
  intro n
  have ht := (NatTrans.mapHomologicalComplex
    (siteSheafTensorRightMap (levelMap B ι n)) (.up ℤ)).naturality a
  change (level B ι (n + 1)).map a ≫ transition B ι P' n =
    transition B ι P n ≫ (level B ι n).map a at ht
  simp [productMap, oneSubShift, Category.assoc, Preadditive.comp_sub,
    Preadditive.sub_comp, ht]

/-- The diagonal product map commutes with the specified differential.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor naturality makes a tensor B_n commute with transition maps. Thus
its product commutes with 1-s as well as d; multiply the two-by-two matrices. -/
theorem roosMap_comm {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)) ≫
        (roos B ι P').d i (i + 1) =
      (roos B ι P).d i (i + 1) ≫
        biprod.map ((productMap B ι a).f (i + 1)) ((productMap B ι a).f ((i + 1) - 1)) := by
  have hs (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j)
    (productMap_oneSubShift B ι a)
  dsimp only [HomologicalComplex.comp_f] at hs
  simp only [roos, CochainComplex.of_d]
  apply biprod.hom_ext
  · simp +instances [roosD, roosX, Category.assoc]
  · simp +instances only [roosX, roosD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.map_fst_assoc,
      eqToHom_naturality_assoc, biprod.map_snd_assoc, HomologicalComplex.Hom.comm,
      biprod.map_snd, biprod.lift_snd_assoc, Preadditive.sub_comp, sub_left_inj]
    rw [hs (i + 1 - 1)]

/-- L(a) applies the product of a tensor B_n to both coordinates.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    roos B ι P ⟶ roos B ι P' :=
  CochainComplex.ofHom
    (fun i => biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)))
    (roosMap_comm B ι a)

private theorem augmentation_naturality {P P' : CochainComplex (Modules R) ℤ}
    (a : P ⟶ P') :
    augmentation B ι P ≫ roosMap B ι a = a ≫ augmentation B ι P' := by
  ext i : 1
  change biprod.lift ((unitProduct B ι P).f i) 0 ≫
    biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)) =
      a.f i ≫ biprod.lift ((unitProduct B ι P').f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    have h : unitProduct B ι P ≫ productMap B ι a = a ≫ unitProduct B ι P' := by
      apply Pi.hom_ext
      intro n
      simp only [unitProduct, productMap, Category.assoc, Pi.map_π, Pi.lift_π_assoc,
        Pi.lift_π]
      exact ((NatTrans.mapHomologicalComplex
        (tensorUnit (ι.app (op n))) (.up ℤ)).naturality a).symm
    exact congrArg (fun f ↦ f.f i) h
  · simp

omit [HasCountableProducts (Modules R)] in
open MonoidalCategory in
private theorem categorical_kflat (P : CochainComplex (Modules R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

set_option maxHeartbeats 400000 in
-- Elaborating the tensor square and single-complex comparison needs extra heartbeats.
omit [HasCountableProducts (Modules R)] in
open MonoidalCategory in
private theorem level_quasiIso {P P' : CochainComplex (Modules R) ℤ}
    (hP : P.IsKFlatIndependentCoefficients) (hP' : P'.IsKFlatIndependentCoefficients)
    (a : P ⟶ P') (ha : QuasiIso a) (n : ℕ) : QuasiIso ((level B ι n).map a) := by
  classical
  let N := (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (levelModule B ι n)
  obtain ⟨K, q, hK, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) N
  let W := HomologicalComplex.quasiIso (Modules R) (.up ℤ)
  have hPcat := categorical_kflat P hP
  have hP'cat := categorical_kflat P' hP'
  have hKcat := categorical_kflat K hK
  have ht : QuasiIso (a ▷ N) := by
    have hq' : W q := hq
    have ha' : W a := ha
    have htop := hKcat.whiskerRight ha'
    have hleft := hPcat.whiskerLeft hq'
    have hright := hP'cat.whiskerLeft hq'
    have hcomp := W.comp_mem _ _ htop hright
    rw [← MonoidalCategory.whisker_exchange a q] at hcomp
    exact (W.precomp_iff _ _ hleft).1 hcomp
  let F := curriedTensor (Modules R)
  let e (L : CochainComplex (Modules R) ℤ) :=
    CochainComplex.mapBifunctorSingle₂Iso F (levelModule B ι n) L ≪≫
      (NatIso.mapHomologicalComplex
        (siteSheafTensorRightIso R (levelModule B ι n)).symm (.up ℤ)).app L
  change QuasiIso (HomologicalComplex.mapBifunctorMap a (𝟙 N) F (.up ℤ)) at ht
  apply (quasiIso_iff_of_arrow_mk_iso
    (HomologicalComplex.mapBifunctorMap a (𝟙 N) F (.up ℤ)) ((level B ι n).map a)
    (Arrow.isoMk (e P) (e P') ?_)).1 ht
  change (e P).hom ≫ ((level B ι n).map a) =
    HomologicalComplex.mapBifunctorMap a (𝟙 N) F (.up ℤ) ≫ (e P').hom
  dsimp only [e, Iso.trans_hom]
  rw [← Category.assoc, CochainComplex.mapBifunctorSingle₂Iso_hom_naturality]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ (CochainComplex.mapBifunctorSingle₂Iso F
    (levelModule B ι n) P).hom ≫ t)
    ((NatIso.mapHomologicalComplex
      (siteSheafTensorRightIso R (levelModule B ι n)).symm (.up ℤ)).hom.naturality a).symm

/-- The strict Roos map preserves quasi-isomorphisms between the specified representatives.
Source: Stacks Tags 06YT and 08TC (blueprint: lem-pe-kflat-roos-representative-invariance).
The tensor square gives a quasi-isomorphism at every tower level. Exact countable
products and the generic Roos coordinate comparison give the asserted quasi-isomorphism. -/
private theorem roosMap_quasiIso_of_kflat
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)]
    [HasDerivedCategory.{w} (Modules R)]
    (P P' : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (_hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i))
    (_hflat' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P'.X i)) :
    ∀ (a : P ⟶ P'), QuasiIso a → QuasiIso (roosMap B ι a) := by
  intro a ha
  have hlevel (n : ℕ) : QuasiIso ((level B ι n).map a) := level_quasiIso B ι hP hP' a ha n
  let f := Discrete.natTrans (F := Discrete.functor (fun n : ℕ ↦ (level B ι n).obj P))
    (G := Discrete.functor (fun n : ℕ ↦ (level B ι n).obj P'))
    (fun n ↦ (level B ι n.as).map a)
  have (n : Discrete ℕ) : QuasiIso (f.app n) := hlevel n.as
  have hp : QuasiIso (productMap B ι a) := HomologicalComplex.quasiIso_limMap f
  exact CochainComplex.quasiIso_of_roos_coordinates
    (product B ι P) (product B ι P') (roos B ι P) (roos B ι P')
    (oneSubShift B ι P) (oneSubShift B ι P')
    (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (productMap B ι a) (roosMap B ι a) (by intro i; rfl) hp

/-- Derived Roos objects attached to derived-isomorphic representatives admit an
augmentation-compatible isomorphism.
Source: Stacks Tags 05RT, 06YS and 08TC (blueprint: lem-pe-kflat-roos-representative-invariance).
A common K-flat roof and the strict naturality equation produce the displayed equality. -/
private theorem exists_derived_roos_comparison
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)]
    [HasDerivedCategory.{w} (Modules R)]
    (P P' : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i))
    (hflat' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P'.X i)) :
    ∀ (e : DerivedCategory.Q.{w}.obj P ≅ DerivedCategory.Q.obj P'),
      ∃ v : DerivedCategory.Q.{w}.obj (roos B ι P) ≅ DerivedCategory.Q.obj (roos B ι P'),
        DerivedCategory.Q.map (augmentation B ι P) ≫ v.hom =
          e.hom ≫ DerivedCategory.Q.map (augmentation B ι P') := by
  classical
  intro e
  obtain ⟨Z, t, ht, f, he⟩ := DerivedCategory.right_fac e.hom
  let := ht
  have ht' : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 ht
  have hf : IsIso (DerivedCategory.Q.map f) := by
    have hh : DerivedCategory.Q.map f = DerivedCategory.Q.map t ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hh]
    infer_instance
  have hf' : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).1 hf
  obtain ⟨W, q, hW, hflatW, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Z
  have hflatW' : ∀ i, IsFlatOnSite (R := R) (W.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (W.X i)).symm
      (hflatW i)
  let := ht'
  let := hf'
  let := hq
  let u := q ≫ t
  let b := q ≫ f
  have hu : QuasiIso u := inferInstance
  have hb : QuasiIso b := inferInstance
  have hLu := roosMap_quasiIso_of_kflat B ι W P hW hP hflatW' hflat u hu
  have hLb := roosMap_quasiIso_of_kflat B ι W P' hW hP' hflatW' hflat' b hb
  let := hLu
  let := hLb
  let v := (asIso (DerivedCategory.Q.map (roosMap B ι u))).symm ≪≫
    asIso (DerivedCategory.Q.map (roosMap B ι b))
  refine ⟨v, ?_⟩
  have hnu := congrArg DerivedCategory.Q.map (augmentation_naturality B ι u)
  have hnb := congrArg DerivedCategory.Q.map (augmentation_naturality B ι b)
  simp only [Functor.map_comp] at hnu hnb
  have hroof : DerivedCategory.Q.map u ≫ e.hom = DerivedCategory.Q.map b := by
    dsimp only [u, b]
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, he,
      IsIso.hom_inv_id_assoc]
  apply (cancel_epi (DerivedCategory.Q.map u)).1
  change DerivedCategory.Q.map u ≫
      (DerivedCategory.Q.map (augmentation B ι P) ≫
        (inv (DerivedCategory.Q.map (roosMap B ι u)) ≫
          DerivedCategory.Q.map (roosMap B ι b))) = _
  calc
    _ = DerivedCategory.Q.map (augmentation B ι W) ≫
        DerivedCategory.Q.map (roosMap B ι b) := by
      rw [← Category.assoc, ← hnu]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = DerivedCategory.Q.map b ≫ DerivedCategory.Q.map (augmentation B ι P') := hnb
    _ = _ := by rw [← hroof, Category.assoc]


/-- Strict and derived invariance of the augmented scalar-extension Roos complex.
Source: Stacks Tags 06YS, 06YT, 06YY and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).

Proof:
1. Resolve each coefficient module in degree zero by a K-flat complex. The tensor
   square and two-out-of-three show that tensoring a quasi-isomorphism between
   K-flat complexes with that coefficient module remains a quasi-isomorphism.
   The single-complex tensor comparison identifies this with the level map.
   Tensor-unit naturality gives the strict augmentation equation.
2. Exact countable products preserve these level quasi-isomorphisms. The generic
   Roos coordinate comparison, proved from degreewise split short exact sequences
   with outer terms V[-1] and V, shows that the diagonal Roos map is a
   quasi-isomorphism.
3. Given e, use lem-pc-right-fraction-representation and
   lem-pc-quasi-isomorphisms-multiplicative-system to represent it by a roof
   Z to P, Z to P'. Both arrows are quasi-isomorphisms. Resolve Z by a K-flat
   flat-term W using lem-pc-kflat-resolution; obtain u:W to P and b:W to P'
   with Q(b) Q(u) inverse = e.
4. Set v = Q(L(b)) Q(L(u)) inverse. Apply Q to the strict augmentation
   equations for u and b to obtain the required augmented comparison equation.
   Since v and e are invertible, Q(eta_P) is invertible iff Q(eta_P') is.
   Cohomology factors through Q, so this is equivalent to the asserted
   quasi-isomorphism criterion for both augmentations. -/
theorem representativeInvariance
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)]
    [HasDerivedCategory.{w} (Modules R)]
    (P P' : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i))
    (hflat' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P'.X i)) :
    (∀ (a : P ⟶ P'), QuasiIso a →
      QuasiIso (roosMap B ι a) ∧
        augmentation B ι P ≫ roosMap B ι a = a ≫ augmentation B ι P') ∧
    (∀ (e : DerivedCategory.Q.{w}.obj P ≅ DerivedCategory.Q.obj P'),
      ∃ v : DerivedCategory.Q.{w}.obj (roos B ι P) ≅ DerivedCategory.Q.obj (roos B ι P'),
        DerivedCategory.Q.map (augmentation B ι P) ≫ v.hom =
          e.hom ≫ DerivedCategory.Q.map (augmentation B ι P')) ∧
    (Nonempty (DerivedCategory.Q.{w}.obj P ≅ DerivedCategory.Q.obj P') →
      (QuasiIso (augmentation B ι P) ↔ QuasiIso (augmentation B ι P'))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    refine ⟨roosMap_quasiIso_of_kflat B ι P P' hP hP' hflat hflat' a ha, ?_⟩
    exact augmentation_naturality B ι a
  · exact exists_derived_roos_comparison B ι P P' hP hP' hflat hflat'
  · rintro ⟨e⟩
    obtain ⟨v, hv⟩ := exists_derived_roos_comparison B ι P P' hP hP' hflat hflat' e
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
      ← DerivedCategory.isIso_Q_map_iff_quasiIso]
    constructor
    · intro h
      let := h
      have : IsIso (e.hom ≫ DerivedCategory.Q.map (augmentation B ι P')) := by
        rw [← hv]
        infer_instance
      exact IsIso.of_isIso_comp_left e.hom _
    · intro h
      let := h
      have : IsIso (DerivedCategory.Q.map (augmentation B ι P) ≫ v.hom) := by
        rw [hv]
        infer_instance
      exact IsIso.of_isIso_comp_right _ v.hom

end SheafOfModules.KFlatRoos
