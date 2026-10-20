/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.CategoryTheory.ConstantFiniteFreeProducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.CategoryTheory.StrictRoosModel
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionResolution
import Mathlib.CategoryTheory.Limits.Final

/-!
# Cofinality of the arithmetic Roos tower

Source: Stacks Project, Cohomology on Sites, Tag 0941, and Modules on Sites,
Tag 03EK; the explicit finite-block comparison and scalar-extension refinement
in the proof of `lem-pur-compact-support-integral-coefficient-comparison`
(blueprint: lem-pur-compact-support-roos-cofinality).

The category parameter below is instantiated by `Mod (underline A)` for a
small site and its constant ring sheaf.  The recorded arithmetic restriction,
selection and block maps are the canonical constructions from Tags 0H9K and
0941.  The proofs use these constructions before passing to the derived category.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC r vA vB w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory

/-- The constant coefficient ring, with its commutative-ring structure forgotten only
when forming its module category. Source: Stacks 03EK and 0941
(blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosRing {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] (A : CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj ((constantSheaf J CommRingCat).obj A)

/-- The recorded module category of the constant coefficient ring.
Source: Stacks 03EK and 0941 (blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosModules {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] (A : CommRingCat.{r}) :=
  ringedSiteModules.{r} (compactRoosRing J A)

/-- Termwise application of an additive functor to a complex.
Source: Stacks 03EK, degree-zero scalar extension
(blueprint: lem-pur-compact-support-roos-cofinality). -/
abbrev compactRoosComplexMap {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise application to the objects and transitions of a strict tower complex.
Source: Stacks 03EK and 0941 (blueprint: lem-pur-compact-support-roos-cofinality). -/
abbrev compactRoosTowerMap {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical tensor/product comparison, determined by all product projections.
Source: Stacks 03EK, finite-dual-basis calculation in the node's proof step 6
(blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosProductComparison
    {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (compactRoosComplexMap F).obj (strictRoosProduct X) ⟶
      strictRoosProduct ((compactRoosTowerMap F).obj X) :=
  piComparison (compactRoosComplexMap F) (fun n : ℕ ↦ X.asFunctor.obj (op n))

section CofinalityConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type u} [Category.{v} D] [Abelian D] [HasCountableProducts D]
private instance cochainCountableProducts : HasCountableProducts (CochainComplex D ℤ) where
  out K _ := by
    have : HasLimitsOfShape (Discrete K) D := inferInstance
    infer_instance

private noncomputable def rho (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e) :
    strictRoosComplex X ⟶ strictRoosComplex ((complexRestriction D e).obj X) :=
  strictRoosMapOfSquare (X := X) (Y := (complexRestriction D e).obj X)
    (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)
private theorem rho_coord (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e)
    (p : ℤ) :
    (rho X e he).f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom =
    (strictRoosCoordinates X p).hom ≫
      biprod.map ((block e X.asFunctor).f p) ((selection e X.asFunctor).f (p + 1)) :=
  strictRoosMapOfSquare_coordinates (X := X)
    (Y := (complexRestriction D e).obj X) _ _ _ _
private theorem coord_ext {Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    {K : CochainComplex D ℤ} {f g : K ⟶ strictRoosComplex Y}
    (h : ∀ p : ℤ, f.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      g.f (p + 1) ≫ (strictRoosCoordinates Y p).hom) : f = g := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  exact (cancel_mono (strictRoosCoordinates Y p).hom).1 (h p)
private theorem selection_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) :
    strictRoosProductMap f ≫ selection e Y.asFunctor =
      selection e X.asFunctor ≫
        strictRoosProductMap ((complexRestriction D e).map f) := by
  let φ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f
  change Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫ selection e Y.asFunctor =
    selection e X.asFunctor ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app ((index e).obj (op n)))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc]
  erw [Pi.map_π]
  unfold selection
  erw [Pi.lift_π_assoc, Pi.lift_π, Pi.map_π]
  rfl

private theorem block_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) :
    strictRoosProductMap f ≫ block e Y.asFunctor =
      block e X.asFunctor ≫
        strictRoosProductMap ((complexRestriction D e).map f) := by
  let φ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f
  change Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫ block e Y.asFunctor =
    block e X.asFunctor ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app ((index e).obj (op n)))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc]
  erw [Pi.map_π]
  unfold block
  erw [Pi.lift_π_assoc, Pi.lift_π]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro k hk
  erw [Pi.map_π_assoc]
  exact congrArg (fun t ↦ Pi.π _ _ ≫ t)
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality _).symm

omit [HasCountableProducts D] in
private theorem biprod_lift_map {P Q P' Q' K : D}
    (a : K ⟶ P) (b : K ⟶ Q) (c : P ⟶ P') (d : Q ⟶ Q') :
    biprod.lift a b ≫ biprod.map c d = biprod.lift (a ≫ c) (b ≫ d) := by
  apply biprod.hom_ext <;> simp

private noncomputable def mu {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y) :
    strictRoosComplex X ⟶ strictRoosComplex Y :=
  strictRoosMapOfSquare _ _ (strictRoosProductMap_comm f)

private theorem mu_coord {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y) (p : ℤ) :
    (mu f).f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫ biprod.map
        ((strictRoosProductMap f).f p) ((strictRoosProductMap f).f (p + 1)) :=
  strictRoosMapOfSquare_coordinates _ _ _ _

attribute [local irreducible] strictRoosMapOfSquare rho mu
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rho_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) (he : 1 ≤ e) :
    mu f ≫ rho Y e he = rho X e he ≫ mu ((complexRestriction D e).map f) := by
  unfold mu rho strictRoosMapOfSquare
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 1
  congr 1
  apply Arrow.hom_ext
  · exact selection_nat f e
  · exact block_nat f e

private theorem roos_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (p : ℤ) :
    roosχ X p = strictRoosCoordinates X p := rfl

private noncomputable def augment (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (P : CochainComplex D ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ,
      γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    P ⟶ strictRoosComplex X := by
  exact roosAugment (X := X) (P := P) γ hγ

private theorem augment_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (P : CochainComplex D ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ,
      γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) (p : ℤ) :
    (augment X P γ hγ).f (p + 1) ≫ (strictRoosCoordinates X p).hom =
      biprod.lift 0 ((Pi.lift γ).f (p + 1)) := by
  rw [← roos_coordinates]
  exact roosAugment_χ γ hγ p

attribute [local irreducible] augment in
attribute [local irreducible] strictRoosComplex strictRoosCoordinates in
private theorem rho_augment (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e)
    (P : CochainComplex D ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ,
      γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    ∃ b : P ⟶ strictRoosComplex X,
      (∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
        biprod.lift 0 ((Pi.lift γ).f (p + 1))) ∧
      ∃ b' : P ⟶ strictRoosComplex ((complexRestriction D e).obj X),
        (∀ p : ℤ, b'.f (p + 1) ≫
          (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom =
          biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ γ (e * (n + 1) - 1))).f (p + 1))) ∧
        b ≫ rho X e he = b' := by
  refine ⟨augment X P γ hγ, augment_coordinates X P γ hγ, ?_⟩
  let γ' (n : ℕ) := γ (e * (n + 1) - 1)
  have hγ' : ∀ n : ℕ, γ' (n + 1) ≫
      (((complexRestriction D e).obj X).asFunctor).map
        (homOfLE (Nat.le_succ n)).op = γ' n := by
    intro n
    exact roos_compatible X.asFunctor γ hγ
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left e (by omega : n + 1 ≤ n + 1 + 1)) 1)
  refine ⟨augment ((complexRestriction D e).obj X) P γ' hγ',
    augment_coordinates ((complexRestriction D e).obj X) P γ' hγ', ?_⟩
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [rho_coord, ← Category.assoc, augment_coordinates, augment_coordinates,
    biprod_lift_map, zero_comp]
  congr 1
  change ((Pi.lift γ ≫ selection e X.asFunctor).f (p + 1)) = _
  congr 1
  apply Pi.hom_ext
  intro n
  simp only [selection, γ', Category.assoc, Pi.lift_π]
  erw [Pi.lift_π]

private theorem index_one_eq : index 1 = 𝟭 (ℕᵒᵖ) := by
  apply Functor.ext
  · intro i j h
    apply Subsingleton.elim
  · intro n
    cases n
    simp [index]

private theorem index_mul_obj (e f n : ℕ) (_he : 1 ≤ e) (hf : 1 ≤ f) :
    e * (f * (n + 1) - 1 + 1) - 1 = (e * f) * (n + 1) - 1 := by
  have hpos : 1 ≤ f * (n + 1) := by nlinarith
  rw [Nat.sub_add_cancel hpos, Nat.mul_assoc]

omit [HasCountableProducts D] in
private theorem restriction_one_eq (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    (complexRestriction D 1).obj X = X := by
  simp only [complexRestriction, restriction, index_one_eq]
  rfl

private theorem square_id {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    (hY : Y = X) (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (ha : HEq a (𝟙 (strictRoosProduct X)))
    (hb : HEq b (𝟙 (strictRoosProduct X)))
    (h : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b) :
    HEq (strictRoosMapOfSquare a b h) (𝟙 (strictRoosComplex X)) := by
  subst Y
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  apply heq_of_eq
  unfold strictRoosMapOfSquare
  have hid : Arrow.homMk (𝟙 (strictRoosProduct X)) (𝟙 (strictRoosProduct X)) h =
      𝟙 (Arrow.mk (strictRoosEndomorphism X)) := by
    apply Arrow.hom_ext <;> rfl
  rw [hid, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  exact (shiftFunctor (CochainComplex D ℤ) (-1 : ℤ)).map_id _

private theorem lift_heq_id {K : Type*} [Category K]
    {f g : ℕ → K} [HasProduct f] [HasProduct g] (h : g = f)
    (t : ∀ n, (∏ᶜ f) ⟶ g n) (ht : ∀ n, HEq (t n) (Pi.π f n)) :
    HEq (Pi.lift t) (𝟙 (∏ᶜ f)) := by
  subst g
  apply heq_of_eq
  apply Pi.hom_ext
  intro n
  rw [Pi.lift_π, Category.id_comp]
  exact eq_of_heq (ht n)

private theorem proj_heq {K : Type*} [Category K] (f : ℕ → K) [HasProduct f]
    {i j : ℕ} (h : i = j) : HEq (Pi.π f i) (Pi.π f j) := by
  subst j
  rfl

private theorem rho_one (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    HEq (rho X 1 (by decide)) (𝟙 (strictRoosComplex X)) := by
  unfold rho
  apply square_id (restriction_one_eq X)
  · apply lift_heq_id
    · funext n
      simp [index]
    · intro n
      exact proj_heq _ (by omega)
  · apply lift_heq_id
    · funext n
      simp [index]
    · intro n
      simp only [Finset.sum_range_one, Nat.add_zero, homOfLE_refl,
        op_id, Functor.map_id, Category.comp_id]
      exact proj_heq _ (by omega)


private theorem index_mul_eq (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    index f ⋙ index e = index (e * f) := by
  apply Functor.ext
  · intro i j h
    apply Subsingleton.elim
  · intro n
    cases n
    exact congrArg op (index_mul_obj e f _ he hf)

private theorem sum_blocks {G : Type*} [AddCommMonoid G] (g : ℕ → G) (e f : ℕ) :
    (∑ k ∈ Finset.range f, ∑ l ∈ Finset.range e, g (e * k + l)) =
      ∑ i ∈ Finset.range (e * f), g i := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]


private theorem lift_heq {K : Type*} [Category K] {P : K}
    {f g : ℕ → K} [HasProduct f] [HasProduct g] (h : f = g)
    (a : ∀ n, P ⟶ f n) (b : ∀ n, P ⟶ g n)
    (ht : ∀ n, HEq (a n) (b n)) : HEq (Pi.lift a) (Pi.lift b) := by
  subst g
  apply heq_of_eq
  congr 1
  funext n
  exact eq_of_heq (ht n)

omit [HasCountableProducts D] in
private theorem restriction_mul_eq (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    (complexRestriction D f).obj ((complexRestriction D e).obj X) =
      (complexRestriction D (e * f)).obj X := by
  have hR : restriction D e ⋙ restriction D f = restriction D (e * f) := by
    simpa only [restriction, Functor.whiskeringLeft_obj_comp] using
      congrArg ((Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ D).obj) (index_mul_eq e f he hf)
  have hobj {F G H : (ℕᵒᵖ ⥤ D) ⥤ (ℕᵒᵖ ⥤ D)}
      [F.Additive] [G.Additive] [H.Additive] (hFG : F ⋙ G = H) :
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj X) =
        (H.mapHomologicalComplex (.up ℤ)).obj X := by
    subst H
    rfl
  exact hobj hR

private theorem comp_lift {K : Type*} [Category K] {P Q : K}
    {g : ℕ → K} [HasProduct g] (a : P ⟶ Q) (b : ∀ n, Q ⟶ g n) :
    a ≫ Pi.lift b = Pi.lift (fun n ↦ a ≫ b n) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_π]

private theorem selection_mul (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    HEq (selection e X.asFunctor ≫
      selection f ((complexRestriction D e).obj X).asFunctor)
      (selection (e * f) X.asFunctor) := by
  unfold selection
  rw [comp_lift]
  apply lift_heq
  · funext n
    exact congrArg (fun m ↦ X.asFunctor.obj (op m)) (index_mul_obj e f n he hf)
  · intro n
    erw [Pi.lift_π]
    exact proj_heq _ (index_mul_obj e f n he hf)

private theorem index_add (e m k : ℕ) (he : 1 ≤ e) :
    e * (m + k + 1) - 1 = (e * (m + 1) - 1) + e * k := by
  have hp : 1 ≤ e * (m + 1) := by nlinarith
  have hm : e * (m + k + 1) = e * (m + 1) + e * k := by ring
  omega

private theorem block_inner (X : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (e m k : ℕ) (he : 1 ≤ e) :
    block e X ≫ Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) (m + k) ≫
        X.map ((index e).map (homOfLE (Nat.le_add_right m k)).op) =
      ∑ l ∈ Finset.range e,
        Pi.π (fun n : ℕ ↦ X.obj (op n)) (e * (m + 1) - 1 + (e * k + l)) ≫
          X.map (homOfLE (Nat.le_add_right (e * (m + 1) - 1) (e * k + l))).op := by
  rw [← Category.assoc, block, Pi.lift_π]
  change (∑ l ∈ Finset.range e,
    Pi.π (fun n : ℕ ↦ X.obj (op n)) (e * (m + k + 1) - 1 + l) ≫
      X.map (homOfLE (Nat.le_add_right (e * (m + k + 1) - 1) l)).op) ≫
    X.map (homOfLE (Nat.sub_le_sub_right
      (Nat.mul_le_mul_left e (by omega : m + 1 ≤ m + k + 1)) 1)).op = _
  simp only [Preadditive.sum_comp, Category.assoc, ← X.map_comp]
  apply Finset.sum_congr rfl
  intro l hl
  have hidx : e * (m + k + 1) - 1 + l =
      e * (m + 1) - 1 + (e * k + l) := by rw [index_add e m k he]; omega
  have hproj (i j n : ℕ) (h : i = j) (hi : n ≤ i) (hj : n ≤ j) :
      Pi.π (fun n : ℕ ↦ X.obj (op n)) i ≫ X.map (homOfLE hi).op =
        Pi.π (fun n : ℕ ↦ X.obj (op n)) j ≫ X.map (homOfLE hj).op := by
    subst j
    rfl
  exact hproj _ _ _ hidx _ _

private theorem block_mul (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    HEq (block e X.asFunctor ≫ block f ((complexRestriction D e).obj X).asFunctor)
      (block (e * f) X.asFunctor) := by
  unfold block
  rw [comp_lift]
  apply lift_heq
  · funext n
    exact congrArg (fun m ↦ X.asFunctor.obj (op m)) (index_mul_obj e f n he hf)
  · intro n
    simp only [Preadditive.comp_sum]
    change HEq
      (∑ k ∈ Finset.range f, block e X.asFunctor ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj ((index e).obj (op n)))
          (f * (n + 1) - 1 + k) ≫
        X.asFunctor.map ((index e).map
          (homOfLE (Nat.le_add_right (f * (n + 1) - 1) k)).op)) _
    simp only [block_inner X.asFunctor e _ _ he]
    have hsum (a b : ℕ) (h : a = b) :
        HEq (∑ i ∈ Finset.range (e * f),
          Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) (a + i) ≫
            X.asFunctor.map (homOfLE (Nat.le_add_right a i)).op)
          (∑ i ∈ Finset.range (e * f),
            Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) (b + i) ≫
              X.asFunctor.map (homOfLE (Nat.le_add_right b i)).op) := by
      subst b
      rfl
    exact (heq_of_eq (sum_blocks (fun i ↦
      Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n))
        (e * (f * (n + 1) - 1 + 1) - 1 + i) ≫
      X.asFunctor.map (homOfLE
        (Nat.le_add_right (e * (f * (n + 1) - 1 + 1) - 1) i)).op) e f)).trans
      (hsum _ _ (index_mul_obj e f n he hf))

private theorem square_comp {X Y Z W : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    (hZW : Z = W)
    (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (c d : strictRoosProduct Y ⟶ strictRoosProduct Z)
    (a' b' : strictRoosProduct X ⟶ strictRoosProduct W)
    (ha : HEq (a ≫ c) a') (hb : HEq (b ≫ d) b')
    (h₁ : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b)
    (h₂ : c ≫ strictRoosEndomorphism Z = strictRoosEndomorphism Y ≫ d)
    (h₃ : a' ≫ strictRoosEndomorphism W = strictRoosEndomorphism X ≫ b') :
    HEq (strictRoosMapOfSquare a b h₁ ≫ strictRoosMapOfSquare c d h₂)
      (strictRoosMapOfSquare a' b' h₃) := by
  subst W
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  apply heq_of_eq
  unfold strictRoosMapOfSquare
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  rfl

private theorem rho_mul (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (e : ℕ) (he : 1 ≤ e) (f : ℕ) (hf : 1 ≤ f) :
    HEq (rho X e he ≫ rho ((complexRestriction D e).obj X) f hf)
      (rho X (e * f) (one_le_mul he hf)) := by
  unfold rho
  exact square_comp (X := X)
    (Y := (complexRestriction D e).obj X)
    (Z := (complexRestriction D f).obj ((complexRestriction D e).obj X))
    (W := (complexRestriction D (e * f)).obj X)
    (restriction_mul_eq X e f he hf) _ _ _ _ _ _
    (selection_mul X e f he hf) (block_mul X e f he hf) _ _ _

private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }

private theorem rho_nat_coordinates {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    (f : X ⟶ Y) (e : ℕ) (he : 1 ≤ e)
    (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
    (μe : strictRoosComplex ((complexRestriction D e).obj X) ⟶
      strictRoosComplex ((complexRestriction D e).obj Y))
    (hμ : ∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫ biprod.map
        ((strictRoosProductMap f).f p) ((strictRoosProductMap f).f (p + 1)))
    (hμe : ∀ p : ℤ, μe.f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj Y) p).hom =
      (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom ≫ biprod.map
        ((strictRoosProductMap ((complexRestriction D e).map f)).f p)
        ((strictRoosProductMap ((complexRestriction D e).map f)).f (p + 1))) :
    μ ≫ rho Y e he = rho X e he ≫ μe := by
  have h₁ : μ = mu f := by
    apply coord_ext
    intro p
    rw [hμ, mu_coord]
  have h₂ : μe = mu ((complexRestriction D e).map f) := by
    apply coord_ext
    intro p
    rw [hμe, mu_coord]
  rw [h₁, h₂]
  exact rho_nat f e he

private theorem limit_selection [HasLimitsOfShape ℕᵒᵖ D]
    (I : ℕᵒᵖ ⥤ CochainComplex D ℤ) (e : ℕ) :
    Pi.lift (fun n : ℕ ↦ limit.π I (op n)) ≫ selection e I =
      limit.pre I (index e) ≫
        Pi.lift (f := fun n : ℕ ↦ I.obj ((index e).obj (op n)))
          (fun n : ℕ ↦ limit.π (index e ⋙ I) (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [selection, Category.assoc, Pi.lift_π, limit.pre_π]
  rfl

attribute [local irreducible] strictRoosComplex strictRoosCoordinates in
private theorem rho_limit_coordinates [HasLimitsOfShape ℕᵒᵖ D]
    (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e)
    (ι : limit I.asFunctor ⟶ strictRoosComplex I)
    (ιe : limit ((complexRestriction D e).obj I).asFunctor ⟶
      strictRoosComplex ((complexRestriction D e).obj I))
    (hι : ∀ p : ℤ, ι.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)))
    (hιe : ∀ p : ℤ, ιe.f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj I) p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
        limit.π ((complexRestriction D e).obj I).asFunctor (op n))).f (p + 1))) :
    ι ≫ rho I e he = limit.pre I.asFunctor (index e) ≫ ιe := by
  apply coord_ext
  intro p
  dsimp only [strictRoosProduct] at hι hιe ⊢
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [rho_coord, ← Category.assoc, hι, hιe, biprod_lift_map, zero_comp]
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.lift_fst, biprod.lift_fst, comp_zero]
  · erw [Category.assoc, biprod.lift_snd, biprod.lift_snd]
    change ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) ≫
      selection e I.asFunctor).f (p + 1)) =
      (limit.pre I.asFunctor (index e) ≫ Pi.lift (fun n : ℕ ↦
        limit.π (((complexRestriction D e).obj I).asFunctor) (op n))).f (p + 1)
    exact congrArg (fun t ↦ t.f (p + 1)) (limit_selection I.asFunctor e)

attribute [local irreducible] strictRoosComplex strictRoosCoordinates

private theorem rho_quasiIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
    (e : ℕ) (he : 1 ≤ e) : QuasiIso (rho X e he) := by
  let D := ringedSiteModules.{max uC vC r} R
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ D)
  obtain ⟨RF, η, hRF, hη, hres, _⟩ :=
    ringedStrictTowerHomotopyLimitOfUniverses.{max uC vC r + 1, uC, vC, r} J R hcomm
  obtain ⟨I, j, hI, hj⟩ := hres X
  have := hI
  have := hj
  have : CochainComplex.IsKInjective ((complexRestriction D e).obj I) :=
    restriction_preservesKInjectives D e he I
  have : QuasiIso ((complexRestriction D e).map j) := inferInstance
  obtain ⟨μ, ι, _, hμ, hι, _, hμq, hιq, _⟩ :=
    strictRoosDerivedLimitComparison.{max uC vC r + 1, uC, vC, r} J R hcomm X I j
  obtain ⟨μe, ιe, _, hμe, hιe, _, hμeq, hιeq, _⟩ :=
    strictRoosDerivedLimitComparison.{max uC vC r + 1, uC, vC, r} J R hcomm
      ((complexRestriction D e).obj X) ((complexRestriction D e).obj I)
      ((complexRestriction D e).map j)
  have : QuasiIso μ := hμq
  have : QuasiIso μe := hμeq
  have : QuasiIso ι := hιq
  have : QuasiIso ιe := hιeq
  let l := limit.pre I.asFunctor (index e)
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have : IsIso l := by dsimp [l]; infer_instance
  have hlim : ι ≫ rho I e he = l ≫ ιe :=
    rho_limit_coordinates I e he ι ιe hι hιe
  have hIq : QuasiIso (rho I e he) := by
    have h : QuasiIso (ι ≫ rho I e he) := by rw [hlim]; infer_instance
    exact (quasiIso_iff_comp_left ι _).mp h
  have hnat : μ ≫ rho I e he = rho X e he ≫ μe :=
    rho_nat_coordinates j e he μ μe hμ hμe
  have : QuasiIso (rho I e he) := hIq
  have h : QuasiIso (rho X e he ≫ μe) := by rw [← hnat]; infer_instance
  exact (quasiIso_iff_comp_right _ μe).mp h

end CofinalityConstruction

attribute [local irreducible] strictRoosComplex strictRoosCoordinates

/-- The cofinal maps are a single family, natural for every strict tower map, with
strict identity and composition after equality transport of the reindexed complexes.
`HEq` expresses that transport without choosing a further isomorphism: the index
functors for iterated restriction and restriction by the product are equal.
The target coordinate is `block` and the source coordinate is `selection`.

Source: Stacks 0941 and 0H9K; explicit proof steps 1--5 of this node
(blueprint: lem-pur-compact-support-roos-cofinality).
Proof:
1. Finite telescoping makes selection and block a commuting square for `1-s`.
   Its shifted cone map has the specified two coordinates.
2. Resolve the tower by a K-injective tower. Arithmetic restriction preserves
   K-injectives and quasi-isomorphisms. The recorded strict Roos comparison
   identifies the two Roos complexes of the resolution with ordinary limits.
   The arithmetic index functor has a right adjoint given by division by e,
   so it is initial and ordinary limit restriction is an isomorphism.
   Coordinate calculations give commuting squares for this limit restriction
   and for the tower resolution. Two-out-of-three proves the specified cone
   map is a quasi-isomorphism.
3. Strict tower maps commute with selection and block. One-term selection and
   block are identities. The index equality for successive restrictions and
   the identity summing blocks of lengths e and f into one block of length ef
   prove strict composition, using functoriality of shifted cone maps.
4. The compatible family has Roos augmentation with coordinates `(0,γ)`.
   Selection restricts that family, and the block map sends zero to zero,
   giving the asserted equality of augmentation maps. -/
theorem compactSupportRoosCofinality
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A : CommRingCat.{max uC vC r})
    [HasExactLimitsOfShape (Discrete ℕ) (compactRoosModules J A)] :
    ∃ ρ : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (e : ℕ) (_he : 1 ≤ e),
        (strictRoosComplex X ⟶
          strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X)),
      (∀ X e he, QuasiIso (ρ X e he) ∧
        ∀ p : ℤ,
          (ρ X e he).f (p + 1) ≫
              (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((block e X.asFunctor).f p)
                ((selection e X.asFunctor).f (p + 1))) ∧
      (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (f : X ⟶ Y) (e : ℕ) (he : 1 ≤ e),
        ∃ (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
          (μe : strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X) ⟶
            strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj Y)),
          (∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((strictRoosProductMap f).f p)
                ((strictRoosProductMap f).f (p + 1))) ∧
          (∀ p : ℤ, μe.f (p + 1) ≫
              (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj Y) p).hom =
            (strictRoosCoordinates ((complexRestriction (compactRoosModules J A) e).obj X) p).hom ≫
              biprod.map ((strictRoosProductMap
                ((complexRestriction (compactRoosModules J A) e).map f)).f p)
                ((strictRoosProductMap
                  ((complexRestriction (compactRoosModules J A) e).map f)).f (p + 1))) ∧
          μ ≫ ρ Y e he = ρ X e he ≫ μe) ∧
      (∀ X, HEq (ρ X 1 (by decide)) (𝟙 (strictRoosComplex X))) ∧
      (∀ X e he f hf,
        HEq (ρ X e he ≫ ρ ((complexRestriction (compactRoosModules J A) e).obj X) f hf)
          (ρ X (e * f) (one_le_mul he hf))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (e : ℕ) (he : 1 ≤ e)
          (P : CochainComplex (compactRoosModules J A) ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)),
        (∀ n : ℕ,
          γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) →
        ∃ b : P ⟶ strictRoosComplex X,
          (∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
            biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) γ).f (p + 1))) ∧
          ∃ b' : P ⟶ strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X),
            (∀ p : ℤ, b'.f (p + 1) ≫
                (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
              biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
                γ (e * (n + 1) - 1))).f (p + 1))) ∧
            b ≫ ρ X e he = b') := by
  refine ⟨rho, ?_, ?_, ?_, ?_, ?_⟩
  · intro X e he
    refine ⟨?_, rho_coord X e he⟩
    apply rho_quasiIso.{uC, vC, r} J (compactRoosRing J A)
    intro U a b
    exact @mul_comm (((constantSheaf J CommRingCat).obj A).obj.obj U) _ a b
  · intro X Y f e he
    exact ⟨mu f, mu ((complexRestriction _ e).map f),
      mu_coord f, mu_coord _, rho_nat f e he⟩
  · exact rho_one
  · exact rho_mul
  · exact rho_augment

section ScalarAugmentation
variable {E : Type u} {H : Type v} [Category.{vA} E] [Category.{vB} H]
    [Abelian E] [Abelian H] [HasCountableProducts E] [HasCountableProducts H]
    (F : E ⥤ H) [F.Additive]

private theorem scalar_augmentation
    (X : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (P : CochainComplex E ℤ)
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (b : P ⟶ strictRoosComplex X)
    (θ : (compactRoosComplexMap F).obj (strictRoosComplex X) ⟶
      strictRoosComplex ((compactRoosTowerMap F).obj X))
    (hθ : ∀ p : ℤ, θ.f (p + 1) ≫
        (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
      F.map (strictRoosCoordinates X p).hom ≫
        F.biprodComparison ((strictRoosProduct X).X p)
          ((strictRoosProduct X).X (p + 1)) ≫
        biprod.map ((compactRoosProductComparison F X).f p)
          ((compactRoosProductComparison F X).f (p + 1)))
    (hb : ∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
      biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) γ).f (p + 1)))
    (p : ℤ) :
    ((compactRoosComplexMap F).map b ≫ θ).f (p + 1) ≫
        (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
      biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦
        ((compactRoosTowerMap F).obj X).asFunctor.obj (op n))
          (fun n : ℕ ↦ (compactRoosComplexMap F).map (γ n))).f (p + 1)) := by
  simp only [HomologicalComplex.comp_f, Category.assoc, hθ]
  change F.map (b.f (p + 1)) ≫ _ = _
  rw [← Category.assoc, ← F.map_comp, hb]
  apply biprod.hom_ext
  · erw [Category.assoc, Category.assoc, biprod.map_fst]
    erw [Functor.biprodComparison_fst_assoc]
    erw [← F.map_comp_assoc, biprod.lift_fst, F.map_zero, zero_comp, biprod.lift_fst]
  · have hp := congrArg (fun f ↦ f.f (p + 1))
      (map_lift_piComparison (compactRoosComplexMap F)
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) P γ)
    erw [Category.assoc, Category.assoc, biprod.map_snd]
    erw [Functor.biprodComparison_snd_assoc]
    erw [← F.map_comp_assoc, biprod.lift_snd, biprod.lift_snd]
    exact hp

omit [HasCountableProducts H] in
private theorem cochain_products [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) (compactRoosComplexMap F) :=
  HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i ↦ by
    change PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.eval E (ComplexShape.up ℤ) i ⋙ F)
    infer_instance)

end ScalarAugmentation

set_option backward.isDefEq.respectTransparency false in
private noncomputable def compactRoosScalarFunctor
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) where
  obj M := SheafOfModules.changeOfRingsOfUniverses α M
  map f := SheafOfModules.changeOfRingsHomOfUniverses α _ f
  map_id M := by
    dsimp [SheafOfModules.changeOfRingsHomOfUniverses,
      SheafOfModules.changeOfRingsOfUniverses]
    rw [← Functor.map_id]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    simp [SheafOfModules.changeOfRingsPresheafOfUniverses]
  map_comp f g := by
    dsimp [SheafOfModules.changeOfRingsHomOfUniverses]
    rw [← Functor.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem compactRoosScalarFunctor_additive
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S) :
    (compactRoosScalarFunctor α).Additive where
  map_add := by
    have : (PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
        (𝟙 (S.obj ⋙ forget₂ CommRingCat RingCat))).Additive :=
      Functor.additive_of_preserves_binary_products _
    intro M N f g
    dsimp [compactRoosScalarFunctor, SheafOfModules.changeOfRingsHomOfUniverses]
    rw [← Functor.map_add]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    let G := ModuleCat.extendScalars (α.hom.app U).hom
    have : G.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_preserves_initial_object
    have : PreservesBinaryBiproducts G :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts G
    have : G.Additive := Functor.additive_of_preservesBinaryBiproducts G
    change G.map (f.val.app U + g.val.app U) = G.map (f.val.app U) + G.map (g.val.app U)
    exact G.map_add

private theorem scalarFunctor_obj
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (compactRoosScalarFunctor α).obj M = SheafOfModules.changeOfRingsOfUniverses α M :=
  rfl

private theorem scalarFunctor_map
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : M ⟶ N) :
    HEq ((compactRoosScalarFunctor α).map f)
      (SheafOfModules.changeOfRingsHomOfUniverses α M f) := HEq.rfl

attribute [local irreducible] compactRoosScalarFunctor
  SheafOfModules.changeOfRingsOfUniverses SheafOfModules.changeOfRingsHomOfUniverses

set_option backward.isDefEq.respectTransparency false in
/-- Finite-free change of constant coefficients commutes canonically with the actual
Roos complex. The functor `F` is fixed on objects and maps by the recorded sheafified
sectionwise change-of-rings construction, rather than an arbitrary tensor operation.
Its target is the category of modules over the constant sheaf of `B`, so every map
and the resulting isomorphism are B-linear. The coordinate equation specifies the
canonical product and biproduct comparisons, including both shifted cone summands.
Naturality, cofinal restriction, and the scalar extension of augmentations are explicit.

Source: Stacks 03EK, 0941 and the finite-dual-basis refinement in proof steps 6--7
(blueprint: lem-pur-compact-support-roos-cofinality).
Proof, following the node's steps 6--7 (using def-pur-sheaf-tensor-product and
 def-weil-pbc-module-tensor-product):
6. Sheafify sectionwise scalar extension and its maps to obtain the additive F
   with exactly the stated object and morphism formulas. Choose a finite A-basis
   b_a of B with dual maps λ_a. The maps m⊗b ↦ (λ_a(b)m)_a and
   (m_a)_a ↦ Σ_a m_a⊗b_a identify scalar extension with a finite power.
   The basis identity holds on the constant presheaf and then on its sheafification.
   The canonical product comparison becomes the rearrangement of a finite power
   of a countable product. Its inverse is Σ_a (m_(i,a))_i⊗b_a, a finite sum of
   sheaf maps. The basis proves invertibility and does not choose the comparison.
7. The product map sends (m_i)_i⊗b to (m_i⊗b)_i on local tensor generators,
   so it is B-linear and natural. The analogous biproduct comparison commutes
   with negatives, internal differentials and shifts. Since the product comparison
   also commutes with the tower shift s, the displayed two-coordinate map is the
   asserted isomorphism θ of actual complexes. Coordinate selection commutes
   with tensor, and a finite transition sum tensored with b is the same finite
   sum of the tensored transitions. This gives the cofinal square. Applying it
   to (0,γ) gives the stated scalar-extended augmentation. Equality on local
   tensor generators descends through sheafification and proves all naturality. -/
theorem compactSupportRoosFiniteFree
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A B : CommRingCat.{max uC vC r}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B]
    [HasExactLimitsOfShape (Discrete ℕ)
      (compactRoosModules J A)] :
    ∃ (F : compactRoosModules J A ⥤
          compactRoosModules J B)
      (_hF : F.Additive),
      (∀ M, F.obj M = SheafOfModules.changeOfRingsOfUniverses
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M) ∧
      (∀ M N (f : M ⟶ N), HEq (F.map f)
        (SheafOfModules.changeOfRingsHomOfUniverses
          ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M f)) ∧
      ∃ θ : ∀ X : CochainComplex
          (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ,
          (compactRoosComplexMap F).obj (strictRoosComplex X) ≅
            strictRoosComplex ((compactRoosTowerMap F).obj X),
        (∀ X (p : ℤ), (θ X).hom.f (p + 1) ≫
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
          F.map (strictRoosCoordinates X p).hom ≫
            F.biprodComparison ((strictRoosProduct X).X p)
              ((strictRoosProduct X).X (p + 1)) ≫
            biprod.map ((compactRoosProductComparison F X).f p)
              ((compactRoosProductComparison F X).f (p + 1))) ∧
        (∀ X Y (f : X ⟶ Y),
          ∃ (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
            (ν : strictRoosComplex ((compactRoosTowerMap F).obj X) ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj Y)),
          (∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((strictRoosProductMap f).f p)
                ((strictRoosProductMap f).f (p + 1))) ∧
          (∀ p : ℤ, ν.f (p + 1) ≫
              (strictRoosCoordinates ((compactRoosTowerMap F).obj Y) p).hom =
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom ≫
              biprod.map ((strictRoosProductMap ((compactRoosTowerMap F).map f)).f p)
                ((strictRoosProductMap ((compactRoosTowerMap F).map f)).f (p + 1))) ∧
          (compactRoosComplexMap F).map μ ≫ (θ Y).hom = (θ X).hom ≫ ν) ∧
        (∀ X (e : ℕ) (_he : 1 ≤ e),
          ∃ (ρ : strictRoosComplex X ⟶ strictRoosComplex
              ((complexRestriction (compactRoosModules J A) e).obj X))
            (ρB : strictRoosComplex ((compactRoosTowerMap F).obj X) ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj
                ((complexRestriction (compactRoosModules J A) e).obj X))),
          (∀ p : ℤ, ρ.f (p + 1) ≫ (strictRoosCoordinates
              ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((block e X.asFunctor).f p)
                ((selection e X.asFunctor).f (p + 1))) ∧
          (∀ p : ℤ, ρB.f (p + 1) ≫ (strictRoosCoordinates ((compactRoosTowerMap F).obj
              ((complexRestriction (compactRoosModules J A) e).obj X)) p).hom =
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom ≫
              biprod.map ((block e ((compactRoosTowerMap F).obj X).asFunctor).f p)
                ((selection e ((compactRoosTowerMap F).obj X).asFunctor).f (p + 1))) ∧
          (compactRoosComplexMap F).map ρ ≫
              (θ ((complexRestriction (compactRoosModules J A) e).obj X)).hom =
            (θ X).hom ≫ ρB) ∧
        (∀ X (P : CochainComplex (compactRoosModules J A) ℤ)
            (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
            (b : P ⟶ strictRoosComplex X),
          (∀ n : ℕ, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) →
          (∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
            biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) γ).f (p + 1))) →
          ∃ bB : (compactRoosComplexMap F).obj P ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj X),
            (∀ p : ℤ, bB.f (p + 1) ≫
                (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
              biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦
                ((compactRoosTowerMap F).obj X).asFunctor.obj (op n))
                  (fun n : ℕ ↦ (compactRoosComplexMap F).map (γ n))).f (p + 1))) ∧
            (compactRoosComplexMap F).map b ≫ (θ X).hom = bB) := by
  let α := (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
  let F : compactRoosModules J A ⥤ compactRoosModules J B :=
    compactRoosScalarFunctor α
  have : F.Additive := compactRoosScalarFunctor_additive α
  have : PreservesLimitsOfShape (Discrete ℕ) F :=
    constantFiniteFree_preservesCountableProducts.{uC, vC, r} J A B F
      (scalarFunctor_obj α)
      (scalarFunctor_map α)
  have : PreservesLimitsOfShape (Discrete ℕ) (compactRoosComplexMap F) :=
    cochain_products F
  obtain ⟨θ, hθ, hnat, hcof⟩ :=
    strictRoosAdditiveComparison F (fun X ↦ by infer_instance)
  refine ⟨F, inferInstance, (scalarFunctor_obj α),
    (scalarFunctor_map α),
    θ, hθ, hnat, hcof, ?_⟩
  intro X P γ b _hγ hb
  refine ⟨(compactRoosComplexMap F).map b ≫ (θ X).hom, ?_, rfl⟩
  exact scalar_augmentation F X P γ b (θ X).hom (hθ X) hb

end CategoryTheory
