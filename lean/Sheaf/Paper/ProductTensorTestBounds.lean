/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Pi.Basic
import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints

/-! # Interval detection by a tensor-compatible product decomposition

Source: main-20261015 blueprint, sec-six-functors-basics/sk-def-purity-conv,
def-pur-section-invariant, final invertibility assertion; Stacks Tag 08FZ
(blueprint: lem-pur-product-tensor-test-bounds).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v ui vi r w wi t

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace SheafOfModules

/-- The recorded module category, forgetting only commutativity of the coefficient ring.
Source: Stacks Modules on Sites (blueprint: lem-pur-product-tensor-test-bounds). -/
abbrev productBoundsModules {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Zero insertion followed by the specified quasi-inverse, with no choice of a lift.
Source: blueprint def-pur-section-invariant, finite-level bounds subargument
(blueprint: lem-pur-product-tensor-test-bounds). -/
def productBoundsInsertion
    {I : Type t} {A : Type u} [Category.{v} A]
    {B : I → Type ui} [∀ i, Category.{vi} (B i)] [∀ i, HasZeroObject (B i)]
    (e : A ≌ (∀ i, B i)) (i : I) (N : B i) : A :=
  e.inverse.obj (fun j ↦ @dite (B j) (i = j) (Classical.propDecidable _)
    (fun h ↦ h ▸ N) (fun _ ↦ (0 : B j)))

/-- Component of the given product equivalence, using the actual coordinate projection.
Source: blueprint def-pur-section-invariant
(blueprint: lem-pur-product-tensor-test-bounds). -/
def productBoundsRestriction
    {I : Type t} {A : Type u} [Category.{v} A]
    {B : I → Type ui} [∀ i, Category.{vi} (B i)]
    (e : A ≌ (∀ i, B i)) (i : I) : A ⥤ B i :=
  e.functor ⋙ Pi.eval B i

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
  {I : Type t} [hI : Finite I]
  {Ci : I → Type ui} [∀ i, Category.{vi} (Ci i)] [∀ i, EssentiallySmall.{r} (Ci i)]
  (Ji : ∀ i, GrothendieckTopology (Ci i)) (Ri : ∀ i, Sheaf (Ji i) CommRingCat.{r})
  [HasDerivedCategory.{w} (productBoundsModules R)]
  [∀ i, HasDerivedCategory.{wi} (productBoundsModules (Ri i))]
  (e : productBoundsModules R ≌ (∀ i, productBoundsModules (Ri i)))
  [∀ i, (productBoundsRestriction e i).Additive]
  [∀ i, PreservesFiniteLimits (productBoundsRestriction e i)]
  [∀ i, PreservesFiniteColimits (productBoundsRestriction e i)]

/-- The induced functor is exactly the descent of degreewise component restriction.
Source: Stacks 05RU and blueprint def-pur-section-invariant
(blueprint: lem-pur-product-tensor-test-bounds). -/
def productBoundsDerived (i : I) :=
  (productBoundsRestriction e i).mapDerivedCategory

attribute [local irreducible] siteDerivedTensorIndependentCoefficients

include hI

/-- Fixed cohomological and Tor intervals are detected componentwise; arbitrary
component modules are tested globally by zero insertion and the given quasi-inverse.
The final clause includes every zero object and every ordered interval.

Source: blueprint def-pur-section-invariant, final invertibility assertion,
finite-level bounds subargument; Stacks sites-cohomology.tex, Tag 08FZ
(blueprint: lem-pur-product-tensor-test-bounds).

Proof:
1. A module A is zero iff all its components are zero: apply faithfulness of e
   to the equality between its identity and zero. Equality of tuples proves this
   also for an empty product; additive component functors preserve zero objects.
2. Apply this criterion to H^m(K), using the assumed natural cohomology comparison
   (def-weil-derived-cohomology-sheaves), and quantify over degrees outside [a,b].
3. Degreewise restriction preserves degree-zero complexes. The counit of e
   identifies r_i(e_i N) with N and other components with zero. The derived
   single-functor comparison and tensor comparison then identify the displayed
   tensor test (def-weil-abstract-derived-category,
   lem-weil-pbc-site-derived-tensor-descent).
4. For global Tor amplitude, test with e_i N for EVERY component module N.
   Steps 2 and 3 give vanishing of each component tensor test in every outside degree.
5. Conversely test with every global M, restrict its tensor with K, and use
   component amplitude on r_i M. Step 2 detects global vanishing. K is unbounded.
6. If I is empty, step 1 makes every global module zero, and the same argument
   proves both vacuous equivalences. Zero has zero cohomology and is K-flat
   (def-pc-kflat-complex); its terms are flat (def-pc-flat-sheaf-modules).
   Total tensor with zero is zero (def-pc-tensor-complex-sheaves), so the K-flat
   representative formula proves the zero-object Tor assertion in every interval.
-/
theorem product_tensor_test_bounds
    (hH : ∀ (i : I) (m : ℤ), Nonempty
      (productBoundsDerived J R Ji Ri e i ⋙ DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙ productBoundsRestriction e i))
    (hT : ∀ i : I, Nonempty
      (siteDerivedTensorIndependentCoefficients J R ⋙ productBoundsDerived J R Ji Ri e i ≅
        (productBoundsDerived J R Ji Ri e i).prod (productBoundsDerived J R Ji Ri e i) ⋙
          siteDerivedTensorIndependentCoefficients (Ji i) (Ri i))) :
    (∀ (K : DerivedCategory (productBoundsModules R)) (a b : ℤ), a ≤ b →
      ((∀ m : ℤ, m ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
        ∀ (i : I) (m : ℤ), m ∉ Set.Icc a b →
          IsZero ((DerivedCategory.homologyFunctor _ m).obj
            ((productBoundsDerived J R Ji Ri e i).obj K))) ∧
      ((∀ (M : productBoundsModules R) (m : ℤ), m ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor _ m).obj
          ((siteDerivedTensorIndependentCoefficients J R).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) ↔
        ∀ (i : I) (N : productBoundsModules (Ri i)) (m : ℤ), m ∉ Set.Icc a b →
          IsZero ((DerivedCategory.homologyFunctor _ m).obj
            ((siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).obj
              ((productBoundsDerived J R Ji Ri e i).obj K,
                (DerivedCategory.singleFunctor _ 0).obj N))))) ∧
    (∀ (i : I) (N : productBoundsModules (Ri i)),
      Nonempty ((productBoundsRestriction e i).obj (productBoundsInsertion e i N) ≅ N) ∧
      ∀ j : I, j ≠ i →
        IsZero ((productBoundsRestriction e j).obj (productBoundsInsertion e i N))) ∧
    (∀ (i : I) (N : productBoundsModules (Ri i))
      (K : DerivedCategory (productBoundsModules R)), Nonempty
        ((productBoundsDerived J R Ji Ri e i).obj
          ((siteDerivedTensorIndependentCoefficients J R).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj (productBoundsInsertion e i N))) ≅
          (siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).obj
            ((productBoundsDerived J R Ji Ri e i).obj K,
              (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    (∀ (K : DerivedCategory (productBoundsModules R)), IsZero K →
      ∀ a b : ℤ, a ≤ b →
        (∀ m : ℤ, m ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ m).obj K)) ∧
        ∀ (M : productBoundsModules R) (m : ℤ), m ∉ Set.Icc a b →
          IsZero ((DerivedCategory.homologyFunctor _ m).obj
            ((siteDerivedTensorIndependentCoefficients J R).obj
              (K, (DerivedCategory.singleFunctor _ 0).obj M)))) := by
  classical
  cases hI
  have hz (M : productBoundsModules R) :
      IsZero M ↔ ∀ i, IsZero ((productBoundsRestriction e i).obj M) := by
    constructor
    · intro h i
      exact (productBoundsRestriction e i).map_isZero h
    · intro h
      apply IsZero.of_full_of_faithful_of_isZero e.functor M
      refine ⟨fun X ↦ ?_, fun X ↦ ?_⟩
      · exact ⟨⟨⟨fun i ↦ (h i).to_ (X i)⟩, fun f ↦ funext fun i ↦
          (h i).eq_of_src _ _⟩⟩
      · exact ⟨⟨⟨fun i ↦ (h i).from_ (X i)⟩, fun f ↦ funext fun i ↦
          (h i).eq_of_tgt _ _⟩⟩
  have hh (K : DerivedCategory (productBoundsModules R)) (m : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ m).obj K) ↔
        ∀ i, IsZero ((DerivedCategory.homologyFunctor _ m).obj
          ((productBoundsDerived J R Ji Ri e i).obj K)) := by
    rw [hz]
    apply forall_congr'
    intro i
    exact ((hH i m).some.app K).isZero_iff.symm
  have hi (i : I) (N : productBoundsModules (Ri i)) :
      Nonempty ((productBoundsRestriction e i).obj (productBoundsInsertion e i N) ≅ N) ∧
      ∀ j : I, j ≠ i →
        IsZero ((productBoundsRestriction e j).obj (productBoundsInsertion e i N)) := by
    let E := fun j ↦ @dite (productBoundsModules (Ri j)) (i = j)
      (Classical.propDecidable _) (fun h ↦ h ▸ N) (fun _ ↦ 0)
    have hc (j : I) :
        (productBoundsRestriction e j).obj (productBoundsInsertion e i N) ≅ E j :=
      (Pi.eval _ j).mapIso (e.counitIso.app E)
    constructor
    · exact ⟨hc i ≪≫ eqToIso (by simp [E])⟩
    · intro j hj
      exact (isZero_zero _).of_iso (hc j ≪≫ eqToIso (by simp [E, Ne.symm hj]))
  have ht (i : I) (K : DerivedCategory (productBoundsModules R))
      (M : productBoundsModules R) :
      (productBoundsDerived J R Ji Ri e i).obj
        ((siteDerivedTensorIndependentCoefficients J R).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).obj
        ((productBoundsDerived J R Ji Ri e i).obj K,
          (DerivedCategory.singleFunctor _ 0).obj ((productBoundsRestriction e i).obj M)) :=
    (hT i).some.app (K, (DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).mapIso
        (Iso.prod (Iso.refl _)
          (((productBoundsRestriction e i).mapDerivedCategorySingleFunctor 0).app M))
  have hti (i : I) (N : productBoundsModules (Ri i))
      (K : DerivedCategory (productBoundsModules R)) :
      (productBoundsDerived J R Ji Ri e i).obj
        ((siteDerivedTensorIndependentCoefficients J R).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj (productBoundsInsertion e i N))) ≅
      (siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).obj
        ((productBoundsDerived J R Ji Ri e i).obj K,
          (DerivedCategory.singleFunctor _ 0).obj N) :=
    ht i K (productBoundsInsertion e i N) ≪≫
      (siteDerivedTensorIndependentCoefficients (Ji i) (Ri i)).mapIso
        (Iso.prod (Iso.refl _) ((DerivedCategory.singleFunctor _ 0).mapIso (hi i N).1.some))
  refine ⟨?_, hi, fun i N K ↦ ⟨hti i N K⟩, ?_⟩
  · intro K a b hab
    constructor
    · constructor
      · intro h i m hm
        exact (hh K m).1 (h m hm) i
      · intro h m hm
        exact (hh K m).2 (fun i ↦ h i m hm)
    · constructor
      · intro h i N m hm
        exact ((DerivedCategory.homologyFunctor _ m).mapIso (hti i N K)).isZero_iff.mp
          ((hh _ m).1 (h (productBoundsInsertion e i N) m hm) i)
      · intro h M m hm
        apply (hh _ m).2
        intro i
        exact ((DerivedCategory.homologyFunctor _ m).mapIso (ht i K M)).isZero_iff.mpr
          (h i ((productBoundsRestriction e i).obj M) m hm)
  · intro K hK a b hab
    constructor
    · intro m hm
      exact (DerivedCategory.homologyFunctor _ m).map_isZero hK
    · intro M m hm
      let L := (DerivedCategory.singleFunctor (productBoundsModules R) 0).obj M
      obtain ⟨_, hA, _⟩ := DerivedTensorConstraints.derived_tensor_additive R L
      let F := (KFlatFixedTensor.derivedTensor R).flip.obj L
      have : F.Additive := hA
      have hF := F.map_isZero hK
      dsimp only [F] at hF
      rw [KFlatFixedTensor.derivedTensor_eq_published] at hF
      exact (DerivedCategory.homologyFunctor _ m).map_isZero hF

end SheafOfModules
