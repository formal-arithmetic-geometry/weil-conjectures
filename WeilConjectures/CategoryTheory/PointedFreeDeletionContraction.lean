/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedInternalBarData
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.CondensedFreeLinearizationTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Universal contraction of the pointed free deletion complex

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
extracted internal bar input (blueprint: lem-sfb-pointed-free-deletion-contraction).

Powers, deletion, and insertion are constructed in condensed sets. Their free maps
use the recorded free adjunction. The existence statement specifies the augmentation
and its section on generalized generators; it is never used to choose any definition.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Preadditive
open Profinite.CondensedAction

namespace Profinite.CondensedAction.PointedDeletion

/-- The condensed sets in the prescribed size convention.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
abbrev Sets := Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))

/-- The actual finite power, including the terminal zero-fold power.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def power (X : Sets.{u}) (n : ℕ) : Sets.{u} := ∏ᶜ fun _ : Fin n ↦ X

/-- Coordinatewise application of a condensed-set map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def powerMap {X Y : Sets.{u}} (f : X ⟶ Y) (n : ℕ) : power X n ⟶ power Y n :=
  Limits.Pi.map fun _ ↦ f

/-- Delete coordinate i, retaining the order of every other coordinate.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def deletion (X : Sets.{u}) (n : ℕ) (i : Fin (n + 1)) :
    power X (n + 1) ⟶ power X n :=
  Pi.lift fun j ↦ Pi.π (fun _ : Fin (n + 1) ↦ X) (i.succAbove j)

/-- Prepend the given global point, with the other coordinates unchanged.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def insertion (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) (n : ℕ) :
    power X n ⟶ power X (n + 1) :=
  Pi.lift (Fin.cases (terminal.from (power X n) ≫ e)
    (fun i ↦ Pi.π (fun _ : Fin n ↦ X) i))

/-- The singleton tuple given by a global point.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def pointTuple (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) : ⊤_ Sets.{u} ⟶ power X 1 :=
  Pi.lift fun _ ↦ e

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Q_n is the canonical free internal module on X^(n+1).
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def term (X : Sets.{u}) (n : ℕ) : Modules R :=
  (InternalBar.free R).obj (power X (n + 1))

/-- The canonical generalized generator, from the fixed adjunction's unit.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def generator (X : Sets.{u}) (n : ℕ) (S : Profinite.{u})
    (x : (power X (n + 1)).obj.obj (op S)) : sectionModule R (term R X n) S :=
  (((InternalBar.freeAdjunction R).unit.app (power X (n + 1))).hom.app (op S)) x

/-- The alternating linearized deletion differential Q_(n+1) → Q_n.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def boundary (X : Sets.{u}) (n : ℕ) : term R X (n + 1) ⟶ term R X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (InternalBar.free R).map (deletion X (n + 1) i)

/-- The actual insertion map h_n, obtained by free linearization.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def homotopy (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) (n : ℕ) :
    term R X n ⟶ term R X (n + 1) :=
  (InternalBar.free R).map (insertion X e (n + 1))

/-- Free coordinatewise maps in each degree.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
def termMap {X Y : Sets.{u}} (f : X ⟶ Y) (n : ℕ) : term R X n ⟶ term R Y n :=
  (InternalBar.free R).map (powerMap f (n + 1))

/-- The normalized contraction for one pointed condensed set. All maps are in the
original internal-module category. The two augmentation maps are fixed on generators;
the other maps are the explicit definitions above. Exact means image equals kernel,
using ShortComplex.Exact, and includes epimorphic augmentation.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
structure Contraction (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) where
  /-- The augmentation d_0. -/
  augmentation : term R X 0 ⟶ Mod.regular R.X
  /-- Every generalized generator is sent to 1. -/
  augmentation_generator : ∀ (S : Profinite.{u})
      (x : (power X 1).obj.obj (op S)),
    InternalBar.onSections R augmentation S (generator R X 0 S x) =
      InternalBar.regularOne R S
  /-- The specified section h_(-1). -/
  section_ : Mod.regular R.X ⟶ term R X 0
  /-- On every test object it sends a to a[e]. The terminal sheaf has one section. -/
  section_formula : ∀ (S : Profinite.{u})
      (t : (⊤_ Sets.{u}).obj.obj (op S))
      (a : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) R.X).obj (op S)),
    InternalBar.onSections R section_ S a =
      a • generator R X 0 S ((pointTuple X e).hom.app (op S) t)
  /-- The generator formula for alternating deletion in all degrees. -/
  boundary_generator : ∀ (n : ℕ) (S : Profinite.{u})
      (x : (power X (n + 2)).obj.obj (op S)),
    InternalBar.onSections R (boundary R X n) S (generator R X (n + 1) S x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        generator R X n S ((deletion X (n + 1) i).hom.app (op S) x)
  /-- The generator formula for insertion of e. -/
  homotopy_generator : ∀ (n : ℕ) (S : Profinite.{u})
      (x : (power X (n + 1)).obj.obj (op S)),
    InternalBar.onSections R (homotopy R X e n) S (generator R X n S x) =
      generator R X (n + 1) S ((insertion X e (n + 1)).hom.app (op S) x)
  /-- The complex condition at augmentation. -/
  boundary_augmentation : boundary R X 0 ≫ augmentation = 0
  /-- The complex condition in every positive degree. -/
  boundary_boundary : ∀ n : ℕ, boundary R X (n + 1) ≫ boundary R X n = 0
  /-- Epsilon h_(-1) = id. -/
  contraction_aug : section_ ≫ augmentation = 𝟙 _
  /-- The degree-zero contracting identity. -/
  contraction_zero : homotopy R X e 0 ≫ boundary R X 0 + augmentation ≫ section_ = 𝟙 _
  /-- The positive-degree contracting identity, with n representing degree n+1. -/
  contraction_succ : ∀ n : ℕ,
    homotopy R X e (n + 1) ≫ boundary R X (n + 1) +
      boundary R X n ≫ homotopy R X e n = 𝟙 _
  /-- Image equals kernel at Q_0. -/
  exact_zero : (ShortComplex.mk (boundary R X 0) augmentation boundary_augmentation).Exact
  /-- Image equals kernel in positive degrees. -/
  exact_succ : ∀ n : ℕ,
    (ShortComplex.mk (boundary R X (n + 1)) (boundary R X n) (boundary_boundary n)).Exact
  /-- Exactness at A. -/
  augmentation_epi : Epi augmentation
  /-- The tensored augmented differential squares to zero, with the left unitor. -/
  tensor_boundary_augmentation : ∀ T : Modules R,
    (boundary R X 0 ▷ T) ≫ (augmentation ▷ T ≫ (λ_ T).hom) = 0
  /-- Every pair of tensored differentials composes to zero. -/
  tensor_boundary_boundary : ∀ (T : Modules R) (n : ℕ),
    (boundary R X (n + 1) ▷ T) ≫ (boundary R X n ▷ T) = 0
  /-- The tensored augmentation has precisely the tensored section. -/
  tensor_contraction_aug : ∀ T : Modules R,
    ((λ_ T).inv ≫ section_ ▷ T) ≫ (augmentation ▷ T ≫ (λ_ T).hom) = 𝟙 T
  /-- The degree-zero contraction after tensoring. -/
  tensor_contraction_zero : ∀ T : Modules R,
    (homotopy R X e 0 ▷ T) ≫ (boundary R X 0 ▷ T) +
      (augmentation ▷ T ≫ (λ_ T).hom) ≫ ((λ_ T).inv ≫ section_ ▷ T) = 𝟙 _
  /-- The positive-degree contraction after arbitrary tensoring. -/
  tensor_contraction_succ : ∀ (T : Modules R) (n : ℕ),
    (homotopy R X e (n + 1) ▷ T) ≫ (boundary R X (n + 1) ▷ T) +
      (boundary R X n ▷ T) ≫ (homotopy R X e n ▷ T) = 𝟙 _
  /-- Image equals kernel at the tensored Q_0. -/
  tensor_exact_zero : ∀ T : Modules R,
    (ShortComplex.mk (boundary R X 0 ▷ T) (augmentation ▷ T ≫ (λ_ T).hom)
      (tensor_boundary_augmentation T)).Exact
  /-- Image equals kernel at each positive tensored degree. -/
  tensor_exact_succ : ∀ (T : Modules R) (n : ℕ),
    (ShortComplex.mk (boundary R X (n + 1) ▷ T) (boundary R X n ▷ T)
      (tensor_boundary_boundary T n)).Exact
  /-- The tensored augmentation is split epic by tensor_contraction_aug. -/
  tensor_augmentation_epi : ∀ T : Modules R, Epi (augmentation ▷ T ≫ (λ_ T).hom)

/-- A family of the normalized contractions, natural for all pointed maps. The degree
minus-one map is the identity on the coefficient ring. No group structure or equivariance
is part of this specification.
Source: blueprint paragraph (3) (blueprint: lem-sfb-pointed-free-deletion-contraction). -/
structure NaturalContraction where
  /-- The contraction on every pointed condensed set. -/
  data : ∀ (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X), Contraction R X e
  /-- Naturality of the augmentation. -/
  augmentation_natural : ∀ (X Y : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
      (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y), e ≫ f = e' →
    termMap R f 0 ≫ (data Y e').augmentation = (data X e).augmentation
  /-- Naturality of h_(-1). -/
  section_natural : ∀ (X Y : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
      (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y), e ≫ f = e' →
    (data X e).section_ ≫ termMap R f 0 = (data Y e').section_
  /-- Naturality of all differentials. -/
  boundary_natural : ∀ (X Y : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
      (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y), e ≫ f = e' → ∀ n : ℕ,
    boundary R X n ≫ termMap R f n = termMap R f (n + 1) ≫ boundary R Y n
  /-- Naturality of every insertion map h_n. -/
  homotopy_natural : ∀ (X Y : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
      (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y), e ≫ f = e' → ∀ n : ℕ,
    homotopy R X e n ≫ termMap R f (n + 1) = termMap R f n ≫ homotopy R Y e' n

section Proof

set_option backward.isDefEq.respectTransparency false

private abbrev augmentation
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u}) :
    term R X 0 ⟶ Mod.regular R.X :=
  (InternalBar.free R).map (CartesianMonoidalCategory.toUnit (power X 1)) ≫ c.unit.hom

private abbrev sectionMap
    (c : Profinite.CondensedFreeLinearization.Comparison R)
    (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) : Mod.regular R.X ⟶ term R X 0 :=
  c.unit.inv ≫ (InternalBar.free R).map
    (terminal.from (𝟙_ Sets.{u}) ≫ pointTuple X e)

private theorem insertion_deletion_zero (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
    (n : ℕ) : insertion X e n ≫ deletion X n 0 = 𝟙 _ := by
  apply Pi.hom_ext
  intro j
  simp [insertion, deletion, power, Category.assoc]

private theorem insertion_deletion_succ (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X)
    (n : ℕ) (i : Fin (n + 1)) :
    insertion X e (n + 1) ≫ deletion X (n + 1) i.succ =
      deletion X n i ≫ insertion X e n := by
  apply Pi.hom_ext
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [insertion, deletion, power, Category.assoc]
  · simp [insertion, deletion, power, Category.assoc]

private theorem deletion_powerMap {X Y : Sets.{u}} (f : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 1)) :
    deletion X n i ≫ powerMap f n = powerMap f (n + 1) ≫ deletion Y n i := by
  apply Pi.hom_ext
  intro j
  simp [deletion, powerMap, power, Category.assoc]

private theorem insertion_powerMap {X Y : Sets.{u}} (e : ⊤_ Sets.{u} ⟶ X)
    (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y) (hf : e ≫ f = e') (n : ℕ) :
    insertion X e n ≫ powerMap f (n + 1) = powerMap f n ≫ insertion Y e' n := by
  apply Pi.hom_ext
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [insertion, powerMap, power, Category.assoc, hf]
  · simp [insertion, powerMap, power, Category.assoc]

private theorem deletion_deletion (X : Sets.{u}) (n : ℕ)
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : j.val ≤ i.val) :
    deletion X (n + 2) j ≫ deletion X (n + 1) i =
      deletion X (n + 2) i.succ ≫
        deletion X (n + 1) (Fin.castLT j (lt_of_le_of_lt h i.isLt)) := by
  apply Pi.hom_ext
  intro k
  simp only [deletion, Category.assoc, Pi.lift_π]
  congr 1
  have hh := Fin.succAbove_succAbove_succAbove_predAbove j i k
  have hi : j.succAbove i = i.succ :=
    Fin.succAbove_of_le_castSucc _ _ h
  have hj : i.predAbove j = Fin.castLT j (lt_of_le_of_lt h i.isLt) := by
    apply Fin.ext
    rw [Fin.predAbove_of_le_castSucc _ _ h]
    rfl
  simpa only [hi, hj] using hh.symm

omit [IsCommMonObj R.X] in
private theorem boundary_boundary (X : Sets.{u}) (n : ℕ) :
    boundary R X (n + 1) ≫ boundary R X n = 0 := by
  classical
  simp only [boundary, comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, i'.castSucc), ?_, ?_⟩
    · intro h
      simp [h] at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · simp only [← Functor.map_comp]
      congr 1
      apply deletion_deletion X n i j
      simpa [S] using hij

private theorem onSections_comp {M N P : Modules R} (f : M ⟶ N) (g : N ⟶ P)
    (S : Profinite.{u}) (x : sectionModule R M S) :
    InternalBar.onSections R (f ≫ g) S x =
      InternalBar.onSections R g S (InternalBar.onSections R f S x) := rfl

private theorem onSections_smul {M N : Modules R} (f : M ⟶ N)
    (S : Profinite.{u})
    (a : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)) (x : sectionModule R M S) :
    InternalBar.onSections R f S (a • x) = a • InternalBar.onSections R f S x := by
  exact (((InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).map f).val.app (op S)).hom.map_smul a x

private theorem augmentation_generator
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (S : Profinite.{u}) (x : (power X 1).obj.obj (op S)) :
    InternalBar.onSections R (augmentation R c X) S (generator R X 0 S x) =
      InternalBar.regularOne R S := by
  rw [augmentation, onSections_comp]
  change InternalBar.onSections R c.unit.hom S
    (InternalBar.onSections R ((InternalBar.free R).map _) S
      (Profinite.CondensedFreeLinearization.generator R _ S x)) = _
  rw [c.map_generator, c.unit_generator]

private theorem boundary_generator
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (n : ℕ) (S : Profinite.{u}) (x : (power X (n + 2)).obj.obj (op S)) :
    InternalBar.onSections R (boundary R X n) S (generator R X (n + 1) S x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        generator R X n S ((deletion X (n + 1) i).hom.app (op S) x) := by
  let E := Mod.forget R.X ⋙
    sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
      (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op S)
  let ev : (term R X (n + 1) ⟶ term R X n) →+ sectionModule R (term R X n) S :=
    (AddMonoidHom.eval (generator R X (n + 1) S x)).comp
      (AddCommGrpCat.homAddEquiv.toAddMonoidHom.comp E.mapAddHom)
  change ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (InternalBar.free R).map (deletion X (n + 1) i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg (fun y ↦ (-1 : ℤ) ^ i.val • y) (c.map_generator _ _ _ S x)

private theorem homotopy_generator
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (e : ⊤_ Sets.{u} ⟶ X) (n : ℕ) (S : Profinite.{u})
    (x : (power X (n + 1)).obj.obj (op S)) :
    InternalBar.onSections R (homotopy R X e n) S (generator R X n S x) =
      generator R X (n + 1) S ((insertion X e (n + 1)).hom.app (op S) x) :=
  c.map_generator _ _ _ S x

private theorem contraction_aug
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (e : ⊤_ Sets.{u} ⟶ X) :
    sectionMap R c X e ≫ augmentation R c X = 𝟙 _ := by
  dsimp [sectionMap, augmentation]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have h : (terminal.from (𝟙_ Sets.{u}) ≫ pointTuple X e) ≫
      CartesianMonoidalCategory.toUnit (power X 1) = 𝟙 _ :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  rw [h, CategoryTheory.Functor.map_id, Category.id_comp, c.unit.inv_hom_id]

omit [IsCommMonObj R.X] in
private theorem boundary_natural {X Y : Sets.{u}} (f : X ⟶ Y) (n : ℕ) :
    boundary R X n ≫ termMap R f n = termMap R f (n + 1) ≫ boundary R Y n := by
  simp only [boundary, termMap, sum_comp, comp_sum, zsmul_comp, comp_zsmul,
    ← Functor.map_comp, deletion_powerMap]

omit [IsCommMonObj R.X] in
private theorem homotopy_natural {X Y : Sets.{u}} (e : ⊤_ Sets.{u} ⟶ X)
    (e' : ⊤_ Sets.{u} ⟶ Y) (f : X ⟶ Y) (hf : e ≫ f = e') (n : ℕ) :
    homotopy R X e n ≫ termMap R f (n + 1) =
      termMap R f n ≫ homotopy R Y e' n := by
  simp only [homotopy, termMap, ← Functor.map_comp, insertion_powerMap e e' f hf]

omit [IsCommMonObj R.X] in
private theorem contraction_succ (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) (n : ℕ) :
    homotopy R X e (n + 1) ≫ boundary R X (n + 1) +
      boundary R X n ≫ homotopy R X e n = 𝟙 _ := by
  simp only [homotopy, boundary, comp_sum, sum_comp, comp_zsmul, zsmul_comp,
    ← Functor.map_comp]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, insertion_deletion_zero,
    CategoryTheory.Functor.map_id,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, insertion_deletion_succ,
    Finset.sum_neg_distrib]
  abel

private theorem augmentation_natural
    (c : Profinite.CondensedFreeLinearization.Comparison R)
    {X Y : Sets.{u}} (f : X ⟶ Y) :
    termMap R f 0 ≫ augmentation R c Y = augmentation R c X := by
  simp only [termMap, augmentation, ← Category.assoc, ← Functor.map_comp]
  congr 2

private theorem section_natural
    (c : Profinite.CondensedFreeLinearization.Comparison R)
    {X Y : Sets.{u}} (e : ⊤_ Sets.{u} ⟶ X) (e' : ⊤_ Sets.{u} ⟶ Y)
    (f : X ⟶ Y) (hf : e ≫ f = e') :
    sectionMap R c X e ≫ termMap R f 0 = sectionMap R c Y e' := by
  simp only [sectionMap, termMap, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Pi.hom_ext
  intro i
  simp [pointTuple, powerMap, power, Category.assoc, hf]

private theorem boundary_augmentation
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u}) :
    boundary R X 0 ≫ augmentation R c X = 0 := by
  simp only [boundary, augmentation, sum_comp, zsmul_comp]
  have h : ∀ i : Fin 2, deletion X 1 i ≫
      CartesianMonoidalCategory.toUnit (power X 1) =
        CartesianMonoidalCategory.toUnit (power X 2) :=
    fun i ↦ CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  simp [h, Fin.sum_univ_two, ← Functor.map_comp_assoc]

private theorem contraction_zero
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (e : ⊤_ Sets.{u} ⟶ X) :
    homotopy R X e 0 ≫ boundary R X 0 +
      augmentation R c X ≫ sectionMap R c X e = 𝟙 _ := by
  have h : insertion X e 1 ≫ deletion X 1 (1 : Fin 2) =
      CartesianMonoidalCategory.toUnit (power X 1) ≫
        terminal.from (𝟙_ Sets.{u}) ≫ pointTuple X e := by
    apply Pi.hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [insertion, deletion, pointTuple, power, Category.assoc]
  dsimp only [homotopy, boundary]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_smul,
    comp_add, comp_neg, ← Functor.map_comp, insertion_deletion_zero,
    CategoryTheory.Functor.map_id, h]
  have ha : augmentation R c X ≫ sectionMap R c X e =
      (InternalBar.free R).map (CartesianMonoidalCategory.toUnit (power X 1) ≫
        terminal.from (𝟙_ Sets.{u}) ≫ pointTuple X e) := by
    dsimp only [augmentation, sectionMap]
    rw [Category.assoc, c.unit.hom_inv_id_assoc, ← Functor.map_comp]
  rw [ha]
  abel

private theorem section_formula
    (c : Profinite.CondensedFreeLinearization.Comparison R) (X : Sets.{u})
    (e : ⊤_ Sets.{u} ⟶ X) (S : Profinite.{u})
    (t : (⊤_ Sets.{u}).obj.obj (op S))
    (a : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)) :
    InternalBar.onSections R (sectionMap R c X e) S a =
      a • generator R X 0 S ((pointTuple X e).hom.app (op S) t) := by
  let t' : (𝟙_ Sets.{u}).obj.obj (op S) := PUnit.unit
  have ht : (terminal.from (𝟙_ Sets.{u})).hom.app (op S) t' = t := by
    let ev := sheafToPresheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⋙
      (evaluation Profinite.{u}ᵒᵖ (Type (u + 1))).obj (op S)
    let : Unique ((⊤_ Sets.{u}).obj.obj (op S)) :=
      Types.isTerminalEquivUnique _
        ((terminalIsTerminal : IsTerminal (⊤_ Sets.{u})).isTerminalObj ev _)
    exact Subsingleton.elim _ _
  have hgen : InternalBar.onSections R (sectionMap R c X e) S
      (InternalBar.regularOne R S) =
      generator R X 0 S ((pointTuple X e).hom.app (op S) t) := by
    rw [← c.unit_generator S t', sectionMap, onSections_comp]
    have hc : InternalBar.onSections R c.unit.inv S
        (InternalBar.onSections R c.unit.hom S
          (Profinite.CondensedFreeLinearization.generator R _ S t')) =
        Profinite.CondensedFreeLinearization.generator R _ S t' := by
      rw [← onSections_comp, c.unit.hom_inv_id]
      rfl
    rw [hc, c.map_generator]
    change generator R X 0 S
      ((pointTuple X e).hom.app (op S)
        ((terminal.from (𝟙_ Sets.{u})).hom.app (op S) t')) = _
    rw [ht]
  have ha : a = a • InternalBar.regularOne R S := by
    change a = a * 1
    exact (mul_one a).symm
  conv_lhs => rw [ha]
  rw [onSections_smul, hgen]

private theorem exact_of_contraction {C : Type*} [Category C] [Abelian C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (h : B ⟶ A) (k : D ⟶ B) (hc : h ≫ f + g ≫ k = 𝟙 B) :
    (ShortComplex.mk f g w).Exact := by
  apply (ShortComplex.mk f g w).exact_iff_kernel_ι_comp_cokernel_π_zero.mpr
  have hh := congrArg (fun t ↦ kernel.ι g ≫ t ≫ cokernel.π f) hc
  simpa [comp_add, add_comp, Category.assoc, kernel.condition_assoc,
    cokernel.condition] using hh.symm

/-- The pointed free deletion complex has the specified natural contraction and is
universally exact under internal relative tensor, without any flatness hypothesis.
Source: blueprint main-20261015, direct-image stability proof, paragraph (3), extracted
internal bar input (blueprint: lem-sfb-pointed-free-deletion-contraction).

Proof:
1. Coordinate deletion and insertion of the global point commute with restriction. Apply
   def-sfb-condensed-free-module-adjunction. The generalized-generator characterization of
   lem-sfb-condensed-free-linearization-tensor gives each displayed formula, including
   epsilon[x] = 1 and h_(-1)(a) = a[e]. This does not assert that sheaf sections are free.
2. Double deletions i < j occur with coefficients (-1)^(i+j) and (-1)^(i+j-1), so cancel.
   At augmentation epsilon([x_1]-[x_0]) = 1-1 = 0.
3. Deleting the inserted point gives the original tuple; the remaining deletions are
   minus insertion after deletion. Hence d h + h d = id, also in degree zero, where
   ([x]-[e])+[e] = [x]. Epsilon h_(-1) = id on the regular module.
4. A pointed map commutes with coordinate deletion and prepending the point. Check on
   generators to obtain all naturality equations, with id_A in degree minus one.
5. Transfer abelianness from sectionwise module sheaves through
   def-weil-pbc-internal-abelian-sheaf-module-equivalence. Compose the contracting identity
   with the kernel inclusion on the left and cokernel projection on the right. Both terms
   vanish, so Mathlib's kernel-cokernel criterion gives exactness. The specified section
   splits augmentation.
6. The internal relative tensor already has the upstream MonoidalPreadditive instance.
   The infrastructure of lem-pe-internal-section-tensor-comparison supplies the required
   colimit preservation of tensoring abelian sheaves. Apply tensorRight T to the complex
   and contracting identities, inserting the left unitor at augmentation. The middle
   unitors cancel in degree zero, yielding exactly the displayed tensored maps.
7. Repeat the kernel-cokernel criterion for the tensored maps. The specified tensored
   section splits augmentation to T. No preservation of kernels by tensor, flatness of T,
   or group law on X is used.
-/
theorem exists_natural_contraction : Nonempty (NaturalContraction R) := by
  classical
  obtain ⟨c⟩ := Profinite.CondensedFreeLinearization.exists_comparison R
  let : Abelian (Modules R) := abelianOfEquivalence
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) R.X).functor
  have epi_of_section {A B : Modules R} (f : A ⟶ B) (s : B ⟶ A)
      (h : s ≫ f = 𝟙 B) : Epi f := by
    let : IsSplitEpi f := ⟨⟨s, h⟩⟩
    infer_instance
  let data (X : Sets.{u}) (e : ⊤_ Sets.{u} ⟶ X) : Contraction R X e := by
    have b0 := boundary_augmentation R c X
    have bb := boundary_boundary R X
    have ca := contraction_aug R c X e
    have c0 := contraction_zero R c X e
    have cs := contraction_succ R X e
    have tb0 (T : Modules R) :
        (boundary R X 0 ▷ T) ≫ (augmentation R c X ▷ T ≫ (λ_ T).hom) = 0 := by
      rw [← Category.assoc, ← comp_whiskerRight, b0,
        MonoidalPreadditive.zero_whiskerRight, zero_comp]
    have tbb (T : Modules R) (n : ℕ) :
        (boundary R X (n + 1) ▷ T) ≫ (boundary R X n ▷ T) = 0 := by
      rw [← comp_whiskerRight, bb, MonoidalPreadditive.zero_whiskerRight]
    have tca (T : Modules R) :
        ((λ_ T).inv ≫ sectionMap R c X e ▷ T) ≫
          (augmentation R c X ▷ T ≫ (λ_ T).hom) = 𝟙 T := by
      simp only [Category.assoc, ← comp_whiskerRight_assoc, ca, id_whiskerRight,
        Category.id_comp, Iso.inv_hom_id]
    have tc0 (T : Modules R) :
        (homotopy R X e 0 ▷ T) ≫ (boundary R X 0 ▷ T) +
          (augmentation R c X ▷ T ≫ (λ_ T).hom) ≫
            ((λ_ T).inv ≫ sectionMap R c X e ▷ T) = 𝟙 _ := by
      have hm := congrArg ((tensorRight T).map) c0
      rw [Functor.map_add, Functor.map_comp, Functor.map_comp,
        CategoryTheory.Functor.map_id] at hm
      change (homotopy R X e 0 ▷ T) ≫ (boundary R X 0 ▷ T) +
        (augmentation R c X ▷ T) ≫ (sectionMap R c X e ▷ T) = 𝟙 _ at hm
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hm
    have tcs (T : Modules R) (n : ℕ) :
        (homotopy R X e (n + 1) ▷ T) ≫ (boundary R X (n + 1) ▷ T) +
          (boundary R X n ▷ T) ≫ (homotopy R X e n ▷ T) = 𝟙 _ := by
      have hm := congrArg ((tensorRight T).map) (cs n)
      rw [Functor.map_add, Functor.map_comp, Functor.map_comp,
        CategoryTheory.Functor.map_id] at hm
      exact hm
    exact
      { augmentation := augmentation R c X
        augmentation_generator := augmentation_generator R c X
        section_ := sectionMap R c X e
        section_formula := section_formula R c X e
        boundary_generator := boundary_generator R c X
        homotopy_generator := homotopy_generator R c X e
        boundary_augmentation := b0
        boundary_boundary := bb
        contraction_aug := ca
        contraction_zero := c0
        contraction_succ := cs
        exact_zero := exact_of_contraction _ _ b0 _ _ c0
        exact_succ := fun n ↦ exact_of_contraction _ _ (bb n) _ _ (cs n)
        augmentation_epi := epi_of_section _ _ ca
        tensor_boundary_augmentation := tb0
        tensor_boundary_boundary := tbb
        tensor_contraction_aug := tca
        tensor_contraction_zero := tc0
        tensor_contraction_succ := tcs
        tensor_exact_zero := fun T ↦ exact_of_contraction _ _ (tb0 T) _ _ (tc0 T)
        tensor_exact_succ := fun T n ↦ exact_of_contraction _ _ (tbb T n) _ _ (tcs T n)
        tensor_augmentation_epi := fun T ↦ epi_of_section _ _ (tca T) }
  exact ⟨{
    data := data
    augmentation_natural := fun X Y e e' f hf ↦ augmentation_natural R c f
    section_natural := fun X Y e e' f hf ↦ section_natural R c e e' f hf
    boundary_natural := fun X Y e e' f hf n ↦ boundary_natural R f n
    homotopy_natural := fun X Y e e' f hf n ↦ homotopy_natural R e e' f hf n }⟩

end Proof

end Profinite.CondensedAction.PointedDeletion
