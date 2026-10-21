/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Sheaf.CategoryTheory.KoszulTensorDerivedTower
import Sheaf.Algebra.Homology.RoosCoordinatesDerivedLimit
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import all Sheaf.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Scalar-linear descent of the explicit Koszul fibre

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
derived.tex, Tags 07KC and 08TC; the explicit coordinate and scalar refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent).

The proposition below packages all the clauses of this single statement. Its witnesses
are constrained by the actual product, differential, diagonal maps, and degree-zero unit.
There is no choice of a cone in a triangulated category in this specification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable (O : Sheaf J CommRingCat.{u})

/-- The displayed product B(M), using the existing strict negative Koszul tower.
Index m means exponent m+1. The dual tower is canonically the ordered tensor of
[O --b_j^(m+1)--> O] in degrees [-r,0], including the empty tensor O[0].
Source: Stacks 0A0E (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProduct (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :=
  ∏ᶜ (fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m))

/-- One minus the actual quotient-tower transition shift on B(M).
Source: Stacks 08TC (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreEndomorphism (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :=
  towerTransitionEndomorphism
    (K := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m)) (fun m ↦
    ((ringedKoszulTensorTower O r b).obj M).map (homOfLE (Nat.le_succ m)).op)

/-- The product of a tensor identity at every tower level, on a chain map.
Source: Stacks 0A0E, explicit refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProductMap (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) :=
  Limits.Pi.map
    (f := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m))
    (g := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj N).obj (op m))
    (fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).map a).app (op m))

/-- The actual degree-zero inclusions into the product B(M).
Source: Stacks 0A0E (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProductUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    M ⟶ koszulFibreProduct O r b M :=
  Pi.lift (fun m : ℕ ↦ ringedKoszulTensorUnitComponent O r b M (op m))

section PublishedData

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- The exact coordinate specification and all descent conclusions of the Koszul fibre
statement. The two `letI` declarations install the previously constructed coefficient
structure and finite biproducts; neither introduces an assumption or chooses an object.
The existential functor is determined up to the unique coordinate isomorphism by its
objects, differentials, maps and unit. In particular, this is not an arbitrary functor
with the right isomorphism classes of values. The derived-limit clause includes its
actual first projection and actual localized tower transitions. The tower comparison
identifies these ordinary tensors, including their transitions, with derived tensors.

Source: Stacks 0A0E, 07KC and 08TC, explicit scalar and coordinate refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent). -/
def KoszulFibreLinearDescentData (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) : Prop :=
  letI := scalarLocalizationCoefficientLinear A O α
  letI := HasFiniteBiproducts.of_hasFiniteProducts
    (C := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  ∃ (F : ringedSiteComplex O ⥤ ringedSiteComplex O)
    (η : 𝟭 (ringedSiteComplex O) ⟶ F)
    (χ : ∀ (M : ringedSiteComplex O) (i : ℤ),
      (F.obj M).X i ≅ (koszulFibreProduct O r b M).X i ⊞
        (koszulFibreProduct O r b M).X (i - 1))
    (π : ∀ M : ringedSiteComplex O, F.obj M ⟶ koszulFibreProduct O r b M),
    (∀ (M : ringedSiteComplex O) (i : ℤ),
      (F.obj M).d i (i + 1) ≫ (χ M (i + 1)).hom =
        (χ M i).hom ≫ biprod.lift
          (biprod.fst ≫ (koszulFibreProduct O r b M).d i (i + 1))
          (biprod.fst ≫ (koszulFibreEndomorphism O r b M).f i ≫
            eqToHom (congrArg (koszulFibreProduct O r b M).X
              (Int.add_sub_cancel i 1).symm) -
            biprod.snd ≫ (koszulFibreProduct O r b M).d (i - 1) ((i + 1) - 1))) ∧
    (∀ (M N : ringedSiteComplex O) (a : M ⟶ N) (i : ℤ),
      (F.map a).f i ≫ (χ N i).hom = (χ M i).hom ≫
        biprod.map ((koszulFibreProductMap O r b a).f i)
          ((koszulFibreProductMap O r b a).f (i - 1))) ∧
    (∀ (M : ringedSiteComplex O) (i : ℤ),
      (η.app M).f i ≫ (χ M i).hom =
        biprod.lift ((koszulFibreProductUnit O r b M).f i) 0) ∧
    (∀ (M : ringedSiteComplex O) (i : ℤ), (π M).f i = (χ M i).hom ≫ biprod.fst) ∧
    (∀ (M N : ringedSiteComplex O) (a a' : M ⟶ N),
      Nonempty (Homotopy a a') → Nonempty (Homotopy (F.map a) (F.map a'))) ∧
    (∀ (M N : ringedSiteComplex O) (a : M ⟶ N), QuasiIso a → QuasiIso (F.map a)) ∧
    F.Additive ∧ F.Linear A ∧
    (∃ (z : F.obj 0 ≅ 0), η.app 0 ≫ z.hom = 0) ∧
    (∀ M N : ringedSiteComplex O,
      IsIso (Functor.biprodComparison F M N) ∧
      η.app (M ⊞ N) ≫ Functor.biprodComparison F M N = biprod.map (η.app M) (η.app N)) ∧
    (∀ (M N M' N' : ringedSiteComplex O) (a : M ⟶ M') (a' : N ⟶ N'),
      F.map (biprod.map a a') ≫ Functor.biprodComparison F M' N' =
        Functor.biprodComparison F M N ≫ biprod.map (F.map a) (F.map a')) ∧
    ∃ (D : ringedSiteDerived O ⥤ ringedSiteDerived O)
      (κ : 𝟭 (ringedSiteDerived O) ⟶ D)
      (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D),
      D.Additive ∧ D.Linear A ∧
      (∀ M : ringedSiteComplex O,
        DerivedCategory.Q.map (η.app M) ≫ (e.app M).hom =
          κ.app (DerivedCategory.Q.obj M)) ∧
      (∀ (M N : ringedSiteDerived O) (a : M ⟶ N) (t : A),
        D.map (t • a) = t • D.map a) ∧
      (∀ M : ringedSiteComplex O,
        Nonempty (((ringedKoszulTensorTower O r b).obj M ⋙ DerivedCategory.Q) ≅
          (ringedKoszulDualTower O r b ⋙ DerivedCategory.Q ⋙
            (SheafOfModules.KFlatFixedTensor.derivedTensor O).obj
              (DerivedCategory.Q.obj M)))) ∧
      (∀ M : ringedSiteComplex O,
        ∃ _hp : HasProduct (fun m : ℕ ↦ DerivedCategory.Q.obj
            (((ringedKoszulTensorTower O r b).obj M).obj (op m))),
          ∃ (p : D.obj (DerivedCategory.Q.obj M) ⟶ ∏ᶜ (fun m : ℕ ↦
              DerivedCategory.Q.obj (((ringedKoszulTensorTower O r b).obj M).obj (op m))))
            (δ : (∏ᶜ (fun m : ℕ ↦ DerivedCategory.Q.obj
              (((ringedKoszulTensorTower O r b).obj M).obj (op m)))) ⟶
                (D.obj (DerivedCategory.Q.obj M))⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun m ↦ DerivedCategory.Q.map
                (((ringedKoszulTensorTower O r b).obj M).map
                  (homOfLE (Nat.le_succ m)).op))
              (D.obj (DerivedCategory.Q.obj M)) p δ ∧
            ∀ m : ℕ, (e.app M).hom ≫ p ≫ Pi.π _ m =
              DerivedCategory.Q.map (π M ≫ Pi.π _ m)) ∧
      HasZeroObject (ObjectProperty.FullSubcategory
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M))) ∧
      HasBinaryBiproducts (ObjectProperty.FullSubcategory
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M))) ∧
      Functor.Linear A (ObjectProperty.ι
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M)))

end PublishedData

section FibreConstruction

private instance fibreHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

private instance fibreAbelian : Abelian
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
  inferInstance

private instance fibreCountableProducts : HasCountableProducts
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
  inferInstance

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory

private instance fibreBiproducts : HasFiniteBiproducts
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def fibreX (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteComplex O) (i : ℤ) :=
  (koszulFibreProduct O r b M).X i ⊞ (koszulFibreProduct O r b M).X (i - 1)

private def fibreD (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteComplex O) (i : ℤ) : fibreX O r b M i ⟶ fibreX O r b M (i + 1) :=
  biprod.lift (biprod.fst ≫ (koszulFibreProduct O r b M).d i (i + 1))
    (biprod.fst ≫ (koszulFibreEndomorphism O r b M).f i ≫
      eqToHom (congrArg (koszulFibreProduct O r b M).X
        (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (koszulFibreProduct O r b M).d (i - 1) ((i + 1) - 1))

private theorem fibreD_sq (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteComplex O) (i : ℤ) :
    fibreD O r b M i ≫ fibreD O r b M (i + 1) = 0 := by
  apply biprod.hom_ext
  · simp [fibreD, Category.assoc]
  · simp +instances only [fibreX, fibreD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.lift_fst_assoc,
      eqToHom_naturality_assoc, eqToHom_refl, Category.id_comp, biprod.lift_snd_assoc,
      Preadditive.sub_comp, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d,
      comp_zero, sub_zero, zero_comp]
    apply sub_eq_zero.mpr
    have hd := eqToHom_naturality
      (fun j : ℤ ↦ (koszulFibreProduct O r b M).d j (i + 1 + 1 - 1))
      (Int.add_sub_cancel i 1).symm
    simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
      congrArg (fun f ↦ biprod.fst ≫ f ≫
        (koszulFibreEndomorphism O r b M).f (i + 1 + 1 - 1)) hd

private def fibreObj (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteComplex O) : ringedSiteComplex O :=
  CochainComplex.of (fibreX O r b M) (fibreD O r b M) (fibreD_sq O r b M)

private theorem fibreProductMap_square (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) :
    koszulFibreProductMap O r b a ≫ koszulFibreEndomorphism O r b N =
      koszulFibreEndomorphism O r b M ≫ koszulFibreProductMap O r b a := by
  apply towerTransitionEndomorphism_natural_backward
  intro n
  exact (((ringedKoszulTensorTower O r b).map a).naturality
    (homOfLE (Nat.le_succ n)).op).symm

private theorem fibreMap_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) (i : ℤ) :
    biprod.map ((koszulFibreProductMap O r b a).f i)
        ((koszulFibreProductMap O r b a).f (i - 1)) ≫ (fibreObj O r b N).d i (i + 1) =
      (fibreObj O r b M).d i (i + 1) ≫
        biprod.map ((koszulFibreProductMap O r b a).f (i + 1))
          ((koszulFibreProductMap O r b a).f ((i + 1) - 1)) := by
  have hs (j : ℤ) := congrArg (fun f ↦ f.f j) (fibreProductMap_square O r b a)
  dsimp only [HomologicalComplex.comp_f] at hs
  simp only [fibreObj, CochainComplex.of_d]
  apply biprod.hom_ext
  · simp +instances [fibreD, fibreX, Category.assoc]
  · simp +instances only [fibreX, fibreD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.map_fst_assoc,
      eqToHom_naturality_assoc, biprod.map_snd_assoc, HomologicalComplex.Hom.comm,
      biprod.map_snd, biprod.lift_snd_assoc, Preadditive.sub_comp, sub_left_inj]
    rw [hs (i + 1 - 1)]

private def fibreMap (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) : fibreObj O r b M ⟶ fibreObj O r b N :=
  CochainComplex.ofHom (fun i ↦ biprod.map ((koszulFibreProductMap O r b a).f i)
    ((koszulFibreProductMap O r b a).f (i - 1))) (fibreMap_comm O r b a)

private theorem fibreProductMap_id (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    koszulFibreProductMap O r b (𝟙 M) = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  simp [koszulFibreProductMap]

private theorem fibreProductMap_comp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N P : ringedSiteComplex O} (a : M ⟶ N) (c : N ⟶ P) :
    koszulFibreProductMap O r b (a ≫ c) =
      koszulFibreProductMap O r b a ≫ koszulFibreProductMap O r b c := by
  apply Pi.hom_ext
  intro n
  simp [koszulFibreProductMap, Category.assoc]

private def fibreFunctor (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O ⥤ ringedSiteComplex O where
  obj := fibreObj O r b
  map := fibreMap O r b
  map_id M := by
    ext i : 1
    simp only [fibreMap, CochainComplex.ofHom, fibreProductMap_id,
      HomologicalComplex.id_f]
    apply biprod.hom_ext <;> simp [fibreObj, fibreX]
  map_comp a c := by
    ext i : 1
    simp only [fibreMap, CochainComplex.ofHom, fibreProductMap_comp,
      HomologicalComplex.comp_f]
    apply biprod.hom_ext <;> simp [Category.assoc]

private theorem fibreProductUnit_zero (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    koszulFibreProductUnit O r b M ≫ koszulFibreEndomorphism O r b M = 0 := by
  apply Pi.hom_ext
  intro n
  ext i : 1
  have h := (ringedKoszulTensorUnitCone O r b M i).w
    (homOfLE (Nat.le_succ n)).op
  change (ringedKoszulTensorUnitComponent O r b M (op (n + 1))).f i ≫
      (((ringedKoszulTensorTower O r b).obj M).map
        (homOfLE (Nat.le_succ n)).op).f i =
    (ringedKoszulTensorUnitComponent O r b M (op n)).f i at h
  simpa only [koszulFibreProductUnit, koszulFibreEndomorphism,
    towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
    Category.id_comp, zero_comp, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.zero_f] using sub_eq_zero.mpr h.symm

private def fibreUnitApp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    M ⟶ fibreObj O r b M :=
  CochainComplex.ofHom (fun i ↦ biprod.lift ((koszulFibreProductUnit O r b M).f i) 0) (by
    intro i
    have h (j : ℤ) := congrArg (fun f ↦ f.f j) (fibreProductUnit_zero O r b M)
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
    simp only [fibreObj, CochainComplex.of_d]
    apply biprod.hom_ext
    · simp [fibreD, Category.assoc]
    · simp [fibreD, Category.assoc, h])

private theorem fibreComponent_natural (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) (n : ℕ) :
    ringedKoszulTensorUnitComponent O r b M (op n) ≫
        ((ringedKoszulTensorTower O r b).map a).app (op n) =
      a ≫ ringedKoszulTensorUnitComponent O r b N (op n) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  dsimp only [ringedKoszulTensorUnitComponent, ringedKoszulTensorTower,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ((ringedKoszulTensor O).map a).naturality]
  change (MonoidalCategory.rightUnitor M).inv ≫
      (a ▷ _) ≫ _ = a ≫ (MonoidalCategory.rightUnitor N).inv ≫ _
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]

private def fibreUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    𝟭 (ringedSiteComplex O) ⟶ fibreFunctor O r b where
  app := fibreUnitApp O r b
  naturality M N a := by
    have h : koszulFibreProductUnit O r b M ≫ koszulFibreProductMap O r b a =
        a ≫ koszulFibreProductUnit O r b N := by
      apply Pi.hom_ext
      intro n
      simpa only [koszulFibreProductUnit, koszulFibreProductMap, Category.assoc,
        Pi.map_π, Pi.lift_π_assoc, Pi.lift_π] using
          fibreComponent_natural O r b a n
    ext i : 1
    change a.f i ≫ biprod.lift _ 0 = biprod.lift _ 0 ≫ biprod.map _ _
    apply biprod.hom_ext
    · simpa [Category.assoc] using (congrArg (fun f ↦ f.f i) h).symm
    · simp

private def fibreProjection (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    fibreObj O r b M ⟶ koszulFibreProduct O r b M :=
  CochainComplex.ofHom (fun _ ↦ biprod.fst) (by
    intro i
    simp [fibreObj, fibreD])

section FibreQuasiIso

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]

private theorem fibreTensor_quasiIso (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) (ha : QuasiIso a) (n : ℕ) :
    QuasiIso (((ringedKoszulTensorTower O r b).map a).app (op n)) := by
  obtain ⟨_, h⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated O
  have hk := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
    (ringed_cech_koszul_dual_tower_isKFlat O r b n)
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := O)
      (((ringedKoszulDualTower O r b).obj (op n)).X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso O _).symm (koszulDual_flat O r b n i)
  exact (h _ hk hf).1 M N a ha |>.2

private theorem fibreProduct_quasiIso (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [CountableAB4Star (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]
    {M N : ringedSiteComplex O} (a : M ⟶ N) (ha : QuasiIso a) :
    QuasiIso (koszulFibreProductMap O r b a) := by
  let α := (ringedKoszulTensorTower O r b).map a
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans
        (F := Discrete.functor (fun n ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op n)))
        (G := Discrete.functor (fun n ↦ ((ringedKoszulTensorTower O r b).obj N).obj (op n)))
        (fun n ↦ α.app (op n.as))).app n) := fibreTensor_quasiIso O r b a ha n.as
  exact HomologicalComplex.quasiIso_limMap _

private theorem fibreFunctor_quasiIso (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [CountableAB4Star (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]
    {M N : ringedSiteComplex O} (a : M ⟶ N) (ha : QuasiIso a) :
    QuasiIso ((fibreFunctor O r b).map a) := by
  apply CochainComplex.quasiIso_of_roos_coordinates
    (koszulFibreProduct O r b M) (koszulFibreProduct O r b N)
    (fibreObj O r b M) (fibreObj O r b N)
    (koszulFibreEndomorphism O r b M) (koszulFibreEndomorphism O r b N)
    (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
    (a := koszulFibreProductMap O r b a)
  · intro i
    simp [fibreObj, fibreD]
  · intro i
    simp [fibreObj, fibreD]
  · intro i
    simp [fibreFunctor, fibreMap]
  · exact fibreProduct_quasiIso O r b a ha

end FibreQuasiIso

private theorem sheafTensorRight_smul (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (M N T : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
    (f : M ⟶ N) (a : A) :
    letI := SheafOfModules.monoidalCategory O
    letI h : Linear A (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
      scalarLocalizationCoefficientLinear A O α
    letI : Module A (M ⟶ N) := h.homModule _ _
    letI : Module A (M ⊗ T ⟶ N ⊗ T) := h.homModule _ _
    (a • f) ▷ T =
      @SMul.smul A (M ⊗ T ⟶ N ⊗ T) (h.homModule _ _).toSMul a (f ▷ T) := by
  let := SheafOfModules.monoidalCategory O
  let h := scalarLocalizationCoefficientLinear A O α
  let : Module A (M ⟶ N) := h.homModule _ _
  let : Module A (M ⊗ T ⟶ N ⊗ T) := h.homModule _ _
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M T).inv).1
  apply (adj.homEquiv (M.val ⊗ T.val) (N ⊗ T)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have h₁ := congrArg (fun h ↦ (h.app U) (x ⊗ₜ[O.obj.obj U] y))
    (PresheafOfModules.tensorPure_natural (a • f) (𝟙 T))
  have h₂ := congrArg (fun h ↦ (h.app U) (x ⊗ₜ[O.obj.obj U] y))
    (PresheafOfModules.tensorPure_natural f (𝟙 T))
  change ((a • f) ▷ T).val.app U _ =
    (α a).val U • (f ▷ T).val.app U _
  simp only [← tensorHom_id] at *
  change ((a • f) ⊗ₘ 𝟙 T).val.app U _ =
    (PresheafOfModules.tensorPure N T).app U
      ((a • f).val.app U x ⊗ₜ[O.obj.obj U] y) at h₁
  change (f ⊗ₘ 𝟙 T).val.app U _ =
    (PresheafOfModules.tensorPure N T).app U
      (f.val.app U x ⊗ₜ[O.obj.obj U] y) at h₂
  change ((a • f) ⊗ₘ 𝟙 T).val.app U
      ((PresheafOfModules.tensorPure M T).app U (x ⊗ₜ[O.obj.obj U] y)) =
    (α a).val U • (f ⊗ₘ 𝟙 T).val.app U
      ((PresheafOfModules.tensorPure M T).app U (x ⊗ₜ[O.obj.obj U] y))
  apply h₁.trans
  apply Eq.trans _ (congrArg (fun z ↦ (α a).val U • z) h₂.symm)
  change (PresheafOfModules.tensorPure N T).app U
    (((α a).val U • f.val.app U x) ⊗ₜ[O.obj.obj U] y) = _
  let c : O.obj.obj U := (α a).val U
  have ht : (c • f.val.app U x) ⊗ₜ[O.obj.obj U] y =
      c • (f.val.app U x ⊗ₜ[O.obj.obj U] y) :=
    (TensorProduct.smul_tmul' _ _ _).symm
  exact (congrArg (fun z ↦ (PresheafOfModules.tensorPure N T).app U z) ht).trans
    (((PresheafOfModules.tensorPure N T).app U).hom.map_smul c _)

private theorem fibreTensor_smul (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (f : M ⟶ N) (a : A) (n : ℕᵒᵖ) :
    letI := scalarLocalizationCoefficientLinear A O α
    ((ringedKoszulTensorTower O r b).map (a • f)).app n =
      a • ((ringedKoszulTensorTower O r b).map f).app n := by
  let := scalarLocalizationCoefficientLinear A O α
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  change HomologicalComplex.mapBifunctorMap (a • f) (𝟙 _)
      (curriedTensor _) (.up ℤ) =
    a • HomologicalComplex.mapBifunctorMap f (𝟙 _) (curriedTensor _) (.up ℤ)
  ext i : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.smul_f_apply, Linear.comp_smul,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    Functor.map_id, Category.id_comp]
  change ((a • f.f p) ▷ _) ≫ _ = a • ((f.f p ▷ _) ≫ _)
  rw [sheafTensorRight_smul O A α]
  exact Linear.smul_comp _ _ _ a _ _

private instance fibreFunctor_linear (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    letI := scalarLocalizationCoefficientLinear A O α
    (fibreFunctor O r b).Linear A := by
  let := scalarLocalizationCoefficientLinear A O α
  constructor
  intro M N f a
  have h : koszulFibreProductMap O r b (a • f) =
      a • koszulFibreProductMap O r b f := by
    apply Pi.hom_ext
    intro n
    simp [koszulFibreProductMap, Linear.smul_comp, fibreTensor_smul O A α]
  ext i : 1
  change biprod.map _ _ = a • biprod.map _ _
  have hi := congrArg (fun f ↦ f.f i) h
  have hj := congrArg (fun f ↦ f.f (i - 1)) h
  dsimp only [HomologicalComplex.smul_f_apply] at hi hj
  rw [hi, hj]
  apply biprod.hom_ext <;> simp [Linear.smul_comp, Linear.comp_smul]

private instance fibreFunctor_additive (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    (fibreFunctor O r b).Additive where
  map_add := by
    intro M N a a'
    ext i : 1
    change biprod.map _ _ = biprod.map _ _ + biprod.map _ _
    have h : koszulFibreProductMap O r b (a + a') =
        koszulFibreProductMap O r b a + koszulFibreProductMap O r b a' := by
      apply Pi.hom_ext
      intro n
      simp only [koszulFibreProductMap, Pi.map_π, Preadditive.add_comp]
      rw [← Preadditive.comp_add]
      congr 1
      let := SheafOfModules.monoidalCategory O
      let := SheafOfModules.symmetricCategory O
      let := Classical.choice (SheafOfModules.tensorClosed O).1
      let := Classical.choice (SheafOfModules.tensorClosed O).2.1
      let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
        SheafOfModules.isGrothendieckAbelian _
      change HomologicalComplex.mapBifunctorMap (a + a') (𝟙 _) _ _ = _
      exact HomologicalComplex.mapBifunctorMap_map_add₁ a a' (𝟙 _)
        (MonoidalCategory.curriedTensor _) (.up ℤ)
    have hi := congrArg (fun f ↦ f.f i) h
    have hj := congrArg (fun f ↦ f.f (i - 1)) h
    dsimp only [HomologicalComplex.add_f_apply] at hi hj
    rw [hi, hj]
    apply biprod.hom_ext <;> simp [Preadditive.add_comp, Preadditive.comp_add]

private def fibreTensorHomotopy {M N : ringedSiteComplex O} {f g : M ⟶ N}
    (h : Homotopy f g) (P : ringedSiteComplex O) :
    Homotopy (((ringedKoszulTensor O).map f).app P)
      (((ringedKoszulTensor O).map g).app P) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  exact HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 P) (curriedTensor _) (.up ℤ)

private theorem fibreTensorHomotopy_natural {M N : ringedSiteComplex O} {f g : M ⟶ N}
    (h : Homotopy f g) {P P' : ringedSiteComplex O} (a : P ⟶ P') (i j : ℤ) :
    (((ringedKoszulTensor O).obj M).map a).f i ≫
        (fibreTensorHomotopy O h P').hom i j =
      (fibreTensorHomotopy O h P).hom i j ≫
        (((ringedKoszulTensor O).obj N).map a).f j := by
  by_cases hij : (ComplexShape.up ℤ).Rel j i
  · let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := Classical.choice (SheafOfModules.tensorClosed O).2.1
    change (HomologicalComplex.mapBifunctorMap (𝟙 M) a
        (curriedTensor _) (.up ℤ)).f i ≫
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 P')
            (curriedTensor _) (.up ℤ)).hom i j =
      (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 P)
          (curriedTensor _) (.up ℤ)).hom i j ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 N) a
          (curriedTensor _) (.up ℤ)).f j
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp +instances only [curriedTensor_obj_obj, HomologicalComplex.mapBifunctorMapHomotopy₁,
      HomologicalComplex.mapBifunctorMapHomotopy.hom₁, ComplexShape.π_def, CochainComplex.prev,
      ComplexShape.ε₁_def, curriedTensor_map_app, HomologicalComplex.id_f, curriedTensor_obj_map,
      whiskerLeft_id, Category.id_comp, one_smul, HomologicalComplex.ι_mapBifunctorMap_assoc,
      Functor.map_id, NatTrans.id_app, HomologicalComplex₂.ι_totalDesc,
      HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc]
    by_cases hpj : (ComplexShape.up ℤ).π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p, q) = j
    · simp +instances only [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hpj,
        HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
        CategoryTheory.Functor.map_id]
      rw [← Category.assoc, whisker_exchange, Category.assoc]
      simp only [NatTrans.id_app, Category.id_comp]
      rfl
    · simp [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hpj]
  · rw [(fibreTensorHomotopy O h P').zero i j hij,
      (fibreTensorHomotopy O h P).zero i j hij, comp_zero, zero_comp]

end FibreConstruction

section ProductHomotopy

variable {C : Type*} [Category C] [Abelian C] [HasCountableProducts C]
  {M N : ℕ → CochainComplex C ℤ} {f g : ∀ n, M n ⟶ N n}

private def productHomotopyHom (h : ∀ n, Homotopy (f n) (g n)) (i j : ℤ) :
    (∏ᶜ M : CochainComplex C ℤ).X i ⟶ (∏ᶜ N : CochainComplex C ℤ).X j :=
  (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) j)
    (limit.isLimit (Discrete.functor N))).lift
      { pt := (∏ᶜ M : CochainComplex C ℤ).X i
        π :=
          { app := fun n ↦ (Pi.π M n.as).f i ≫ (h n.as).hom i j
            naturality := by
              rintro ⟨n⟩ ⟨m⟩ e
              have he : n = m := Discrete.eq_of_hom e
              subst m
              simp } }

@[reassoc]
private theorem productHomotopyHom_π (h : ∀ n, Homotopy (f n) (g n)) (i j : ℤ) (n : ℕ) :
    productHomotopyHom h i j ≫ (Pi.π N n).f j = (Pi.π M n).f i ≫ (h n).hom i j :=
  (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) j)
    (limit.isLimit (Discrete.functor N))).fac _ ⟨n⟩

private def productHomotopy (h : ∀ n, Homotopy (f n) (g n)) :
    Homotopy (Limits.Pi.map f) (Limits.Pi.map g) where
  hom := productHomotopyHom h
  zero i j hij := by
    apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) j)
      (limit.isLimit (Discrete.functor N))).hom_ext
    rintro ⟨n⟩
    change productHomotopyHom h i j ≫ (Pi.π N n).f j = 0 ≫ (Pi.π N n).f j
    rw [productHomotopyHom_π, (h n).zero i j hij, comp_zero, zero_comp]
  comm i := by
    apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i)
      (limit.isLimit (Discrete.functor N))).hom_ext
    rintro ⟨n⟩
    change (Limits.Pi.map f).f i ≫ (Pi.π N n).f i =
      (dNext i (productHomotopyHom h) +
        prevD i (productHomotopyHom h) + (Limits.Pi.map g).f i) ≫
          (Pi.π N n).f i
    simp only [dNext, prevD,
      AddMonoidHom.mk'_apply, Preadditive.add_comp, Category.assoc]
    rw [← (Pi.π N n).comm, productHomotopyHom_π_assoc,
      productHomotopyHom_π, ← (Pi.π M n).comm_assoc]
    have hf := congrArg (fun a ↦ a.f i) (Limits.Pi.map_π f n)
    have hg := congrArg (fun a ↦ a.f i) (Limits.Pi.map_π g n)
    dsimp only [HomologicalComplex.comp_f] at hf hg
    rw [hf, hg, (h n).comm i]
    simp [dNext, prevD, Preadditive.comp_add]

private theorem productHomotopy_transition
    (a : ∀ n, M (n + 1) ⟶ M n) (b : ∀ n, N (n + 1) ⟶ N n)
    (h : ∀ n, Homotopy (f n) (g n))
    (hw : ∀ n i j, (a n).f i ≫ (h n).hom i j =
      (h (n + 1)).hom i j ≫ (b n).f j) (i j : ℤ) :
    (towerTransitionEndomorphism a).f i ≫ (productHomotopy h).hom i j =
      (productHomotopy h).hom i j ≫ (towerTransitionEndomorphism b).f j := by
  have hu (K : ℕ → CochainComplex C ℤ) (s : ∀ n, K (n + 1) ⟶ K n)
      (k : ℤ) (n : ℕ) :
      (towerTransitionEndomorphism s).f k ≫ (Pi.π K n).f k =
        (Pi.π K n).f k - (Pi.π K (n + 1)).f k ≫ (s n).f k := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply] using
      congrArg (fun t ↦ t.f k)
        ((towerTransitionEndomorphism_eq_iff s (towerTransitionEndomorphism s)).1 rfl n)
  apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) j)
    (limit.isLimit (Discrete.functor N))).hom_ext
  rintro ⟨n⟩
  change (_ ≫ productHomotopyHom h i j) ≫ (Pi.π N n).f j =
    (productHomotopyHom h i j ≫ _) ≫ (Pi.π N n).f j
  rw [Category.assoc, productHomotopyHom_π, ← Category.assoc, hu M a i n,
    Category.assoc, hu N b j n]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    productHomotopyHom_π, productHomotopyHom_π_assoc, hw]

end ProductHomotopy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def fibreProductHomotopy (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} {f g : M ⟶ N} (h : Homotopy f g) :
    Homotopy (koszulFibreProductMap O r b f) (koszulFibreProductMap O r b g) :=
  productHomotopy (fun n ↦ fibreTensorHomotopy O h
    ((ringedKoszulDualTower O r b).obj (op n)))

private theorem fibreProductHomotopy_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} {f g : M ⟶ N} (h : Homotopy f g) (i j : ℤ) :
    (koszulFibreEndomorphism O r b M).f i ≫
        (fibreProductHomotopy O r b h).hom i j =
      (fibreProductHomotopy O r b h).hom i j ≫
        (koszulFibreEndomorphism O r b N).f j := by
  exact productHomotopy_transition
    (M := fun n ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op n))
    (N := fun n ↦ ((ringedKoszulTensorTower O r b).obj N).obj (op n))
    (fun n ↦ ((ringedKoszulTensorTower O r b).obj M).map
      (homOfLE (Nat.le_succ n)).op)
    (fun n ↦ ((ringedKoszulTensorTower O r b).obj N).map
      (homOfLE (Nat.le_succ n)).op)
    (fun n ↦ fibreTensorHomotopy O h ((ringedKoszulDualTower O r b).obj (op n)))
    (fun n i j ↦ fibreTensorHomotopy_natural O h
      ((ringedKoszulDualTower O r b).map (homOfLE (Nat.le_succ n)).op) i j) i j

private theorem cochainNext (i : ℤ) : (ComplexShape.up ℤ).next i = i + 1 :=
  (ComplexShape.up ℤ).next_eq' rfl

private theorem cochainPrev (i : ℤ) : (ComplexShape.up ℤ).prev i = i - 1 :=
  (ComplexShape.up ℤ).prev_eq' (by change (i - 1) + 1 = i; omega)

section SignedHomotopy

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]

private abbrev signedFibreX (V : CochainComplex C ℤ) (i : ℤ) := V.X i ⊞ V.X (i - 1)

private def signedFibreD (V : CochainComplex C ℤ) (u : V ⟶ V) (i : ℤ) :
    signedFibreX V i ⟶ signedFibreX V (i + 1) :=
  biprod.lift (biprod.fst ≫ V.d i (i + 1))
    (biprod.fst ≫ u.f i ≫ eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))

private theorem signedFibreD_sq (V : CochainComplex C ℤ) (u : V ⟶ V) (i : ℤ) :
    signedFibreD V u i ≫ signedFibreD V u (i + 1) = 0 := by
  apply biprod.hom_ext
  · simp [signedFibreD, Category.assoc]
  · simp only [signedFibreX, signedFibreD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.lift_fst_assoc,
      eqToHom_naturality_assoc, eqToHom_refl, Category.id_comp, biprod.lift_snd_assoc,
      Preadditive.sub_comp, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d,
      comp_zero, sub_zero, zero_comp]
    apply sub_eq_zero.mpr
    have hd := eqToHom_naturality (fun j : ℤ ↦ V.d j (i + 1 + 1 - 1))
      (Int.add_sub_cancel i 1).symm
    simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
      congrArg (fun f ↦ biprod.fst ≫ f ≫ u.f (i + 1 + 1 - 1)) hd

private abbrev signedFibre (V : CochainComplex C ℤ) (u : V ⟶ V) : CochainComplex C ℤ :=
  CochainComplex.of (signedFibreX V) (signedFibreD V u) (signedFibreD_sq V u)

@[reassoc]
private theorem signedFibre_eqToHom_fst (V : CochainComplex C ℤ) (i j : ℤ) (h : i = j) :
    eqToHom (congrArg (signedFibreX V) h) ≫ biprod.fst =
      biprod.fst ≫ eqToHom (congrArg V.X h) := by
  subst j
  simp

@[reassoc]
private theorem signedFibre_eqToHom_snd (V : CochainComplex C ℤ) (i j : ℤ) (h : i = j) :
    eqToHom (congrArg (signedFibreX V) h) ≫ biprod.snd =
      biprod.snd ≫ eqToHom (congrArg (fun k ↦ V.X (k - 1)) h) := by
  subst j
  simp

omit [HasBinaryBiproducts C] in
@[reassoc]
private theorem homotopy_eqToHom {V W : CochainComplex C ℤ} {f g : V ⟶ W}
    (h : Homotopy f g) (i j k : ℤ) (hij : i = j) :
    eqToHom (congrArg V.X hij) ≫ h.hom j k = h.hom i k := by
  subst j
  simp

private def signedFibreHomotopy
    (V W : CochainComplex C ℤ) (u : V ⟶ V) (v : W ⟶ W)
    {f g : V ⟶ W} (h : Homotopy f g)
    (F G : signedFibre V u ⟶ signedFibre W v)
    (hF : ∀ i, F.f i = biprod.map (f.f i) (f.f (i - 1)))
    (hG : ∀ i, G.f i = biprod.map (g.f i) (g.f (i - 1)))
    (hw : ∀ i j, u.f i ≫ h.hom i j = h.hom i j ≫ v.f j) : Homotopy F G where
  hom i j := biprod.map (h.hom i j) (-h.hom (i - 1) (j - 1))
  zero i j hij := by
    have h' : ¬ (ComplexShape.up ℤ).Rel (j - 1) (i - 1) := by
      change ¬ (j - 1) + 1 = i - 1
      change ¬ j + 1 = i at hij
      omega
    rw [h.zero i j hij, h.zero (i - 1) (j - 1) h']
    apply biprod.hom_ext <;> simp
  comm i := by
    have hc := h.comm i
    have hc' := h.comm (i - 1)
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hc hc'
    erw [cochainNext, cochainPrev] at hc hc'
    rw [hF, hG]
    let T := signedFibreX V i ⟶ signedFibreX W i
    let add (a b : T) : T := a + b
    change biprod.map (f.f i) (f.f (i - 1)) = add (add
      ((signedFibre V u).d i ((ComplexShape.up ℤ).next i) ≫
        biprod.map (h.hom ((ComplexShape.up ℤ).next i) i)
          (-h.hom ((ComplexShape.up ℤ).next i - 1) (i - 1)))
      (biprod.map (h.hom i ((ComplexShape.up ℤ).prev i))
          (-h.hom (i - 1) ((ComplexShape.up ℤ).prev i - 1)) ≫
        (signedFibre W v).d ((ComplexShape.up ℤ).prev i) i))
      (biprod.map (g.f i) (g.f (i - 1)))
    dsimp only [add]
    erw [cochainNext, cochainPrev]
    apply biprod.hom_ext <;> apply biprod.hom_ext'
    all_goals
      simp +instances only [hc, hc', biprod.map_fst, biprod.map_snd, Preadditive.comp_add,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inr_fst_assoc, BinaryBicone.inl_snd_assoc,
        BinaryBicone.inr_snd_assoc, zero_comp, add_zero, signedFibreX,
        CochainComplex.of.d, ↓reduceDIte, signedFibreD, add_sub_cancel_right,
        eqToHom_naturality, eqToHom_refl, Category.comp_id, sub_add_cancel]
      erw [Preadditive.add_comp, Preadditive.add_comp]
      simp +instances only [Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.comp_add,
        Preadditive.comp_neg, Preadditive.sub_comp, Preadditive.comp_sub, neg_sub,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inr_fst_assoc, BinaryBicone.inl_snd_assoc,
        BinaryBicone.inr_snd_assoc, zero_comp, zero_add, add_zero, zero_eq_neg,
        zero_sub, sub_zero, biprod.inl_map_assoc, biprod.inr_map_assoc,
        Preadditive.neg_comp, add_left_inj, add_right_inj, hw]
      first
      | erw [signedFibre_eqToHom_fst]
      | erw [signedFibre_eqToHom_snd]
      simp +instances only [biprod.lift_fst_assoc, biprod.lift_snd_assoc,
        Preadditive.sub_comp, Category.assoc, sub_add_cancel, eqToHom_naturality,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Preadditive.comp_sub,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inr_fst_assoc,
        BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_comp, comp_zero,
        sub_zero, zero_sub, Preadditive.comp_neg, neg_neg, add_left_inj]
    all_goals first
    | omega
    | erw [homotopy_eqToHom_assoc h i (i + 1 - 1) (i - 1) (by omega)]
      simp
    | exact congrArg (fun k ↦ V.d (i - 1) k ≫ h.hom k (i - 1))
        (show i - 1 + 1 = i + 1 - 1 by omega)

end SignedHomotopy

private def fibreHomotopy (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} {f g : M ⟶ N} (h : Homotopy f g) :
    Homotopy ((fibreFunctor O r b).map f) ((fibreFunctor O r b).map g) :=
  signedFibreHomotopy (koszulFibreProduct O r b M) (koszulFibreProduct O r b N)
    (koszulFibreEndomorphism O r b M) (koszulFibreEndomorphism O r b N)
    (fibreProductHomotopy O r b h)
    ((fibreFunctor O r b).map f) ((fibreFunctor O r b).map g)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fibreProductHomotopy_comm O r b h)

private theorem additive_linear_descent
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    (A : Type*) [CommRing A] [Linear A C]
    (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ) [F.Additive] [F.Linear A]
    (η : 𝟭 (CochainComplex C ℤ) ⟶ F)
    (hq : ∀ {M N : CochainComplex C ℤ} (a : M ⟶ N),
      QuasiIso a → QuasiIso (F.map a)) :
    ∃ (D : DerivedCategory.{w} C ⥤ DerivedCategory.{w} C)
      (κ : 𝟭 (DerivedCategory.{w} C) ⟶ D)
      (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D),
      D.Additive ∧ D.Linear A ∧
      ∀ M : CochainComplex C ℤ,
        DerivedCategory.Q.map (η.app M) ≫ (e.app M).hom =
          κ.app (DerivedCategory.Q.obj M) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  have hinv : W.IsInvertedBy (F ⋙ DerivedCategory.Q) := by
    intro M N a ha
    have : QuasiIso (F.map a) := hq a ha
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (F.map a)))
  let D := Localization.lift (F ⋙ DerivedCategory.Q) hinv DerivedCategory.Q
  let e := (Localization.fac (F ⋙ DerivedCategory.Q) hinv DerivedCategory.Q).symm
  have : (DerivedCategory.Q ⋙ D).Additive := Functor.additive_of_iso e
  have : ((HomotopyCategory.quotient C (.up ℤ)) ⋙ (DerivedCategory.Qh ⋙ D)).Additive :=
    Functor.additive_of_iso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) D).symm
  have : (DerivedCategory.Qh ⋙ D).Additive :=
    Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient C (.up ℤ)) _
  have : D.Additive := (Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) D).2 inferInstance
  have : D.Linear A := (Localization.functor_linear_iff DerivedCategory.Q W A
    (F ⋙ DerivedCategory.Q) D).1 inferInstance
  let ν : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory.{w} C) ⟶ DerivedCategory.Q ⋙ D :=
    (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight η DerivedCategory.Q ≫ e.hom
  let κ := Localization.liftNatTrans DerivedCategory.Q W _ _ (𝟭 (DerivedCategory.{w} C)) D ν
  refine ⟨D, κ, e, inferInstance, inferInstance, ?_⟩
  intro M
  simp [κ, ν]

private theorem unit_biprod {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] (F : C ⥤ C) (η : 𝟭 C ⟶ F) (X Y : C) :
    η.app (X ⊞ Y) ≫ Functor.biprodComparison F X Y = biprod.map (η.app X) (η.app Y) := by
  apply biprod.hom_ext <;> simp [Functor.biprodComparison, ← η.naturality]

private theorem unit_complete_subcategory {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (F : C ⥤ C) [F.Additive]
    (η : 𝟭 C ⟶ F) :
    HasZeroObject (ObjectProperty.FullSubcategory (fun X : C ↦ IsIso (η.app X))) ∧
      HasBinaryBiproducts
        (ObjectProperty.FullSubcategory (fun X : C ↦ IsIso (η.app X))) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  let P : ObjectProperty C := fun X ↦ IsIso (η.app X)
  have hzero : P 0 :=
    (isZero_zero C).isIso (F.map_isZero (isZero_zero C)) (η.app 0)
  have : P.ContainsZero := ⟨⟨0, isZero_zero C, hzero⟩⟩
  have : P.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    let : IsIso (η.app X) := hX
    have he : η.app Y = e.inv ≫ η.app X ≫ F.map e.hom := by
      have h := η.naturality e.hom
      simpa using congrArg (fun f ↦ e.inv ≫ f) h
    change IsIso (η.app Y)
    rw [he]
    infer_instance⟩
  have hb (X Y : C) (hX : P X) (hY : P Y) : P (X ⊞ Y) := by
    let : IsIso (η.app X) := hX
    let : IsIso (η.app Y) := hY
    have h : IsIso (η.app (X ⊞ Y) ≫ Functor.biprodComparison F X Y) := by
      rw [unit_biprod]
      change IsIso (biprod.mapIso (asIso (η.app X)) (asIso (η.app Y))).hom
      infer_instance
    have : IsIso (Functor.biprodComparison F X Y) := by
      change IsIso (F.mapBiprod X Y).hom
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Functor.biprodComparison F X Y)
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact P.prop_of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (hb _ _ (hD ⟨.left⟩) (hD ⟨.right⟩)))
  exact ⟨inferInstance, HasBinaryBiproducts.of_hasBinaryProducts⟩

attribute [-instance] fibreHasSheafCompose fibreAbelian fibreCountableProducts

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]

/-- The explicit product fibre descends to an additive A-linear completion functor,
with its specified unit and additive full subcategory of complete objects.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
derived.tex, Tags 07KC and 08TC; explicit scalar-linear refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent).

Proof (the node's ten steps):
1. The two-term transition square is b^m b = b^(m+1). Tensor the factors, with
   the signed total differential. Their terms are finite free, including r=0.
2. Bounded-above flat sheaf complexes are K-flat (lem-pc-bounded-above-flat-kflat-site).
   Fixed K-flat tensor preserves quasi-isomorphisms and computes derived tensor,
   naturally in the fixed argument (lem-weil-pbc-kflat-fixed-tensor-triangulated).
3. Set u=1-s. The mixed terms in d_F squared cancel because u is a chain map.
   Products of a tensor 1 commute with u. Check identities, composition, addition
   and scalar multiplication at every product projection.
4. Tensor a chain homotopy with 1. The cross signs are (-1)^(p-1) and (-1)^p.
   The fibre homotopy is (h_B,-h_B); its mixed term u h_B-h_B u is zero.
5. Exact countable products compute derived products
   (lem-weil-derived-countable-products-core). Thus B(a) is a quasi-isomorphism;
   apply lem-pe-roos-coordinates-quasi-iso to the diagonal fibre map.
6. Descend QF by lem-weil-pbc-localization-universal-property. Additivity descends
   by lem-pur-additive-localization-descent. The canonical derived A-action and Q's
   linearity are lem-weil-linear-abelian-derived-category; use
   lem-sfb-linear-localization-descent to cover every derived morphism.
7. The actual projections make QB the derived product. In cone coordinates the
   chain isomorphism is (x,y) to (-y,x), with inverse (v,w) to (w,-v).
   Rotate its cone triangle, obtaining the Roos triangle of def-weil-derived-limit.
8. The degree-zero inclusions give e:M to B(M), with ue=0. The unit is (e,0).
   Check naturality at projections, then descend it by localization's universal
   property. This fixes the unit, without claiming uniqueness from level maps alone.
9. Distribute tensor and products over zero and binary sums in both fibre coordinates.
   These canonical comparisons are natural and identify the units; localization
   preserves the identities, and Q is additive.
10. The zero unit is invertible. A sum of invertible units is invertible by the
    preceding comparison. Fullness gives inherited Hom A-modules and bilinear
    composition. This proves the stated additive full subcategory. -/
theorem koszulFibreLinearDescent (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [CountableAB4Star (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :
    KoszulFibreLinearDescentData O A α r b := by
  let := scalarLocalizationCoefficientLinear A O α
  let := HasFiniteBiproducts.of_hasFiniteProducts
    (C := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let F := fibreFunctor O r b
  let η := fibreUnit O r b
  let π := fibreProjection O r b
  let := fibreFunctor_linear O A α r b
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  refine ⟨F, η, (fun M i ↦ Iso.refl _), π, ?_, ?_, ?_, ?_, ?_, ?_,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro M i
    simp [F, fibreFunctor, fibreObj, fibreD]
  · intro M N a i
    simp [F, fibreFunctor, fibreMap]
  · intro M i
    simp [η, fibreUnit, fibreUnitApp]
  · intro M i
    rfl
  · intro M N a a' ⟨h⟩
    exact ⟨fibreHomotopy O r b h⟩
  · intro M N a ha
    exact fibreFunctor_quasiIso O r b a ha
  · exact ⟨(F.map_isZero (isZero_zero _)).isoZero, (isZero_zero _).eq_of_src _ _⟩
  · intro M N
    exact ⟨by change IsIso (F.mapBiprod M N).hom; infer_instance,
      unit_biprod F η M N⟩
  · intro M N M' N' a a'
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.biprodComparison_fst,
        Functor.biprodComparison_fst_assoc, biprod.map_fst]
      rw [← F.map_comp, biprod.map_fst, F.map_comp]
    · simp only [Category.assoc, Functor.biprodComparison_snd,
        Functor.biprodComparison_snd_assoc, biprod.map_snd]
      rw [← F.map_comp, biprod.map_snd, F.map_comp]
  · obtain ⟨D, κ, e, hDa, hDl, hη⟩ := additive_linear_descent A F η
      (fun a ha ↦ fibreFunctor_quasiIso O r b a ha)
    let := hDa
    let := hDl
    obtain ⟨hzero, hbiprod⟩ := unit_complete_subcategory D κ
    refine ⟨D, κ, e, hDa, hDl, hη, ?_, koszulTensorDerivedTower O r b,
      ?_, hzero, hbiprod, inferInstance⟩
    · intro M N a t
      exact D.map_smul t a
    · intro M
      obtain ⟨hp, p, δ, ht, hproj⟩ :=
        CochainComplex.derivedLimitTriangle_of_roos_coordinates
          (fun n : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op n))
          (fun n ↦ ((ringedKoszulTensorTower O r b).obj M).map
            (homOfLE (Nat.le_succ n)).op)
          (F.obj M) (fun _ ↦ Iso.refl _)
          (by intro i; simp [F, fibreFunctor, fibreObj, fibreD])
          (π M) (by intro i; rfl)
      let := hp
      refine ⟨hp, (e.app M).inv ≫ p,
        δ ≫ (shiftFunctor (ringedSiteDerived O) (1 : ℤ)).map (e.app M).hom, ?_, ?_⟩
      · unfold IsDerivedLimitTriangle at ht ⊢
        apply Pretriangulated.isomorphic_distinguished _ ht
        exact Pretriangulated.Triangle.isoMk _ _ (e.app M).symm (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp [Category.assoc, ← Functor.map_comp])
      · intro n
        simpa [Category.assoc] using hproj n

end CategoryTheory
