/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Finite filtered objects and their bounded-below localization

Source: Stacks Project, Derived Categories, Sections 13.13 and 13.20, Tags 05S2,
05TW, 05TY and 015Q (blueprint: def-trf-finite-filtered-localization).

`none` allows all finite filtrations, with bounds depending on the object.
`some (a,b)` requires the fixed interval `Fᵃ = ⊤`, `Fᵇ⁺¹ = ⊥`.
The Boolean parameter selects all objects or the full subcategory of filtered injectives.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The additive subgroup of maps preserving all filtration steps.
Source: Stacks, Homology, Tag 0121
(blueprint: def-trf-finite-filtered-localization). -/
def filteredHomSubgroup (K L : FilteredObject C) : AddSubgroup (K.obj ⟶ L.obj) where
  carrier := fun f ↦ ∀ p : ℤ, ∃ l : (K.filtration.step p : C) ⟶
    (L.filtration.step p : C), l ≫ (L.filtration.step p).arrow =
      (K.filtration.step p).arrow ≫ f
  zero_mem' := fun p ↦ ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg p
    obtain ⟨f', hf'⟩ := hf p
    obtain ⟨g', hg'⟩ := hg p
    exact ⟨f' + g', by simp [hf', hg', Preadditive.comp_add]⟩
  neg_mem' := by
    intro f hf p
    obtain ⟨f', hf'⟩ := hf p
    exact ⟨-f', by simp [hf']⟩

/-- The existing filtered morphisms identified with their additive subgroup.
Source: Stacks, Tag 0121 (blueprint: def-trf-finite-filtered-localization). -/
def filteredHomEquiv (K L : FilteredObject C) :
    (K ⟶ L) ≃ filteredHomSubgroup K L where
  toFun f := ⟨f.hom, f.preserves⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Addition of filtered maps is addition of underlying maps.
Source: Stacks, Derived Categories, Section 13.13
(blueprint: def-trf-finite-filtered-localization). -/
instance filteredObjectPreadditive : Preadditive (FilteredObject C) where
  homGroup K L := (filteredHomEquiv K L).addCommGroup
  add_comp := by
    intro K L M f g h
    apply (filteredHomEquiv K M).injective
    apply Subtype.ext
    exact Preadditive.add_comp _ _ _ f.hom g.hom h.hom
  comp_add := by
    intro K L M f g h
    apply (filteredHomEquiv K M).injective
    apply Subtype.ext
    exact Preadditive.comp_add _ _ _ f.hom g.hom h.hom

/-- Finite decreasing filtrations, optionally in a prescribed interval, optionally with
injective graded objects. No uniform bound is imposed across terms of a complex.
Source: Stacks, Tags 0121, 05TW and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredProperty (B : Option (ℤ × ℤ)) (inj : Bool) :
    ObjectProperty (FilteredObject C) := fun K ↦
  K.filtration.IsFinite ∧
    (∀ a b : ℤ, B = some (a, b) →
      K.filtration.step a = ⊤ ∧ K.filtration.step (b + 1) = ⊥) ∧
    (∀ p : ℤ, inj = true → Injective (K.filtration.gradedPiece p))

/-- The full additive category of finite filtered objects (`inj = false`) or filtered
injective objects (`inj = true`), with optional fixed filtration bounds.
Source: Stacks, Tags 0121 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredObjects (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (inj : Bool) :=
  (finiteFilteredProperty (C := C) B inj).FullSubcategory

variable (C)

/-- These full subcategories have finite products. The products are the ordinary
finite direct sums with the direct-sum filtration, including the empty sum.
Source: Stacks, Section 13.13 and Tag 015Q.
Proof: take finite biproducts of the underlying objects and their filtration steps.
The inclusions of the summed steps are monic. Common lower and upper bounds for
finitely many finite filtrations give finiteness; prescribed bounds are retained.
Their graded objects are the finite sums of the original graded objects. Finite
sums of injectives are injective. The componentwise projections and lifts satisfy
the product universal property in the full subcategory.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFiltered_hasFiniteProducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteProducts (FiniteFilteredObjects C B inj) := by
  sorry

attribute [instance] finiteFiltered_hasFiniteProducts

/-- The zero object supplied by the empty product in a preadditive category.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasZeroObject (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasZeroObject (FiniteFilteredObjects C B inj) :=
  hasZeroObject_of_hasTerminal_object

/-- Finite biproducts supplied by finite products and addition of filtered maps.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasFiniteBiproducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteBiproducts (FiniteFilteredObjects C B inj) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Binary biproducts from the existing finite biproduct structure.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasBinaryBiproducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasBinaryBiproducts (FiniteFilteredObjects C B inj) :=
  hasBinaryBiproducts_of_finite_biproducts (FiniteFilteredObjects C B inj)

/-- The inclusion of filtered injectives into finite filtered objects.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
def filteredInjectiveInclusion (B : Option (ℤ × ℤ)) :
    FiniteFilteredObjects C B true ⥤ FiniteFilteredObjects C B false :=
  ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.1, fun _ hfalse ↦ by cases hfalse⟩)

/-- The inclusion preserves addition, as both full subcategories use underlying addition.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
instance filteredInjectiveInclusion_additive (B : Option (ℤ × ℤ)) :
    (filteredInjectiveInclusion C B).Additive where
  map_add := rfl

/-- Graded maps preserve identities.
Source: Stacks, Tags 0121 and 012K.
Proof: the identity on the graded cokernel has the required composite with its
projection; the cokernel universal property makes it the canonical graded map.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredGraded_map_id (B : Option (ℤ × ℤ)) (inj : Bool) (p : ℤ)
    (K : FiniteFilteredObjects C B inj) :
    FilteredObject.gradedMapSteps (𝟙 K.obj) p = 𝟙 _ := by
  sorry

/-- Graded maps preserve composition.
Source: Stacks, Tags 0121 and 012K.
Proof: compose the two restriction squares and then the two cokernel squares.
Uniqueness of factorization through the monic inclusions and uniqueness of
cokernel descent identify this composite with the graded map of the composite.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredGraded_map_comp (B : Option (ℤ × ℤ)) (inj : Bool) (p : ℤ)
    {K L M : FiniteFilteredObjects C B inj} (f : K ⟶ L) (g : L ⟶ M) :
    FilteredObject.gradedMapSteps (f ≫ g).hom p =
      FilteredObject.gradedMapSteps f.hom p ≫ FilteredObject.gradedMapSteps g.hom p := by
  sorry

/-- Forget the filtration (`none`) or take a graded piece (`some p`).
The graded map is the existing canonical map on the cokernels of successive steps.
Source: Stacks, Tags 0121 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def filteredEvaluation (B : Option (ℤ × ℤ)) (inj : Bool) (p : Option ℤ) :
    FiniteFilteredObjects C B inj ⥤ C :=
  match p with
  | none =>
    { obj := fun K ↦ K.obj.obj
      map := fun f ↦ f.hom.hom }
  | some p =>
    { obj := fun K ↦ K.obj.filtration.gradedPiece p
      map := fun f ↦ FilteredObject.gradedMapSteps f.hom p
      map_id := filteredGraded_map_id C B inj p
      map_comp := filteredGraded_map_comp C B inj p }

/-- Forgetting and taking graded pieces are additive functors.
Source: Stacks, Section 13.13 and Tag 015Q.
Proof: restrictions of a sum are sums by uniqueness through monic inclusions.
Passing this equality through the cokernel projections proves additivity of the
graded map. The forgetful case is the definition of addition on filtered maps.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredEvaluation_additive (B : Option (ℤ × ℤ)) (inj : Bool) (p : Option ℤ) :
    (filteredEvaluation C B inj p).Additive := by
  sorry

attribute [instance] filteredEvaluation_additive

/-- `K_F⁺(C)`: bounded-below complexes of finite filtered objects modulo filtered homotopy.
For `inj = true` this is `K⁺(Iᶠ)`; chain homotopies take values in the filtered category.
Source: Stacks, Tags 05TW, 05TY and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredHomotopyPlus (B : Option (ℤ × ℤ)) (inj : Bool) :=
  HomotopyCategory.Plus (FiniteFilteredObjects C B inj)

/-- The filtered quasi-isomorphisms are precisely maps inducing quasi-isomorphisms
on every graded complex, using the canonical graded functors on homotopy categories.
Source: Stacks, Tags 05S2 and 05TY
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredQuasiIso (B : Option (ℤ × ℤ)) :
    MorphismProperty (FiniteFilteredHomotopyPlus C B false) := fun _ _ f ↦
  ∀ p : ℤ, HomotopyCategory.Plus.quasiIso C
    ((filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus.map f)

/-- Filtered quasi-isomorphisms admit a left calculus of fractions.
Source: Stacks, Section 13.13, construction of the filtered derived category.
Proof: the cone of a filtered quasi-isomorphism is graded acyclic. Graded acyclic
objects form a triangulated subcategory because grading is additive and preserves
mapping-cone triangles. Thus filtered quasi-isomorphisms are exactly the Verdier
class of that subcategory, which has the calculus of fractions. All mapping cones
remain bounded below and, for fixed bounds, retain the same filtration interval.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFilteredQuasiIso_leftFractions (B : Option (ℤ × ℤ)) :
    (finiteFilteredQuasiIso C B).HasLeftCalculusOfFractions := by
  sorry

attribute [instance] finiteFilteredQuasiIso_leftFractions

/-- The graded quasi-isomorphisms are compatible with the standard cone triangulation.
Source: Stacks, Section 13.13, Tag 05S2.
Proof: grading commutes with shifts and cones. Its acyclic objects are triangulated,
and the cone criterion identifies their Verdier class with graded quasi-isomorphisms.
The triangulated-subcategory localization criterion gives the claimed compatibility.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFilteredQuasiIso_triangulation (B : Option (ℤ × ℤ)) :
    (finiteFilteredQuasiIso C B).IsCompatibleWithTriangulation := by
  sorry

attribute [instance] finiteFilteredQuasiIso_triangulation

/-- `DF⁺(C)`, constructed by formally inverting graded quasi-isomorphisms in `K_F⁺(C)`.
Its triangulation is the standard triangulated localization, not an arbitrary structure.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredDerivedPlus (B : Option (ℤ × ℤ)) :=
  (finiteFilteredQuasiIso C B).Localization

/-- The canonical filtered localization functor.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev finiteFilteredQh (B : Option (ℤ × ℤ)) :
    FiniteFilteredHomotopyPlus C B false ⥤ FiniteFilteredDerivedPlus C B :=
  (finiteFilteredQuasiIso C B).Q

/-- The canonical functor `K⁺(Iᶠ) → DF⁺(C)`, induced by inclusion and localization.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
def filteredInjectiveComparison (B : Option (ℤ × ℤ)) :
    FiniteFilteredHomotopyPlus C B true ⥤ FiniteFilteredDerivedPlus C B :=
  (filteredInjectiveInclusion C B).mapHomotopyCategoryPlus ⋙ finiteFilteredQh C B

/-- The comparison commutes with the standard cochain shifts using the inclusion
and localization shift comparisons.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
instance filteredInjectiveComparison_commShift (B : Option (ℤ × ℤ)) :
    (filteredInjectiveComparison C B).CommShift ℤ :=
  inferInstanceAs (((filteredInjectiveInclusion C B).mapHomotopyCategoryPlus ⋙
    finiteFilteredQh C B).CommShift ℤ)

variable [HasDerivedCategory.{w} C]

/-- Forgetting and grading invert filtered quasi-isomorphisms after ordinary localization.
Source: Stacks, Tags 05S2 and 015Q.
Proof: for grading this is the defining condition on the map. For forgetting, a
filtered acyclic cone is acyclic: in each degree its finite filtration is exhaustive
and separated, and exactness of every graded complex implies exactness of the
underlying complex. The ordinary derived localization therefore inverts the map.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredEvaluation_inverts (B : Option (ℤ × ℤ)) (p : Option ℤ) :
    (finiteFilteredQuasiIso C B).IsInvertedBy
      ((filteredEvaluation C B false p).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) := by
  sorry

/-- The canonical forgetful or graded functor `DF⁺(C) → D⁺(C)`, defined by localization
of the corresponding operation on filtered complexes.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredDerivedEvaluation (B : Option (ℤ × ℤ)) (p : Option ℤ) :
    FiniteFilteredDerivedPlus C B ⥤ DerivedCategory.Plus C :=
  Localization.Construction.lift
    ((filteredEvaluation C B false p).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh) (filteredEvaluation_inverts C B p)

end CategoryTheory
