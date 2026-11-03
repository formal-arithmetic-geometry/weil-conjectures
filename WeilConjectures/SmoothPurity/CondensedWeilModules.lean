/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-! # Weil pairs on actual condensed modules

Source: latest blueprint, def-weil-weil-sheaf-complex, Weil-module and constructible
Weil-sheaf paragraphs (blueprint: def-weil-weil-sheaf-complex).

Weil modules are fixed pairs for exact pullback on actual condensed modules.
Weil complexes live in the ordinary derived category of those Weil modules.
Strict Weil complexes are pairs in the underlying bounded constructible derived category.
The canonical realization forgets a derived Weil module and retains its derived structure
isomorphism; it does not identify the two categories or assert faithfulness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- Actual Weil modules are the existing fixed-pair category on module pullback.
Source: latest blueprint, the displayed theta in the Weil-module paragraph
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedWeilModules
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ Y) :=
  CategoryTheory.Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g)

/-- Constructible Weil sheaves form the full subcategory with constructible carrier.
Source: latest blueprint, Sh_c,W as a full subcategory of actual Weil modules
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedConstructibleWeilSheaves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ Y) :=
  ObjectProperty.FullSubcategory (fun M : condensedWeilModules Λ g ↦
    IsConstructibleModuleObject (condensedRingObj Λ Y) M.carrier)

/-- A constructible Weil module placed in degree zero, in the recorded bounded
constructible category. Its carrier is the actual single complex, with no descent input.
Source: the degree-zero Weil-sheaf clause (blueprint: def-weil-weil-sheaf-complex). -/
def condensedWeilSingle (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}} (g : Y ⟶ Y)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l) g) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)).FullSubcategory :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj M.obj.carrier,
    CondensedRing.boundedConstructible_singleFunctor_obj
      (Profinite.padicAlgClRingObj l) Y 0 M.obj.carrier M.property⟩

/-- Forget the structure isomorphism of an actual Weil module.
Source: the forgetful functor in the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedWeilModuleForget :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget (CondensedRing.upperStar Λ g)

/-- Bounded complexes of Weil modules with constructible underlying cohomology.
This is a property in the ordinary derived category of Weil modules, before forgetting.
Source: the paragraph "Weil complexes" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
def condensedWeilComplexProperty : ObjectProperty (DerivedCategory (condensedWeilModules Λ g)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructibleModuleObject (condensedRingObj Λ Y)
      (((DerivedCategory.homologyFunctor _ n).obj K).carrier)

/-- The actual bounded constructible derived category of Weil modules.
Source: the paragraph "Weil complexes" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedWeilComplex := (condensedWeilComplexProperty Λ g).FullSubcategory

/-- Strict Weil complexes are bounded constructible pairs in the underlying derived category.
Source: the paragraph "Strict Weil complexes" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev condensedStrictWeilComplex :=
  ObjectProperty.FullSubcategory
    (fun K : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar Λ g).mapDerivedCategory ↦
        boundedConstructible (condensedRingObj Λ Y) K.carrier)

/-- Exact forgetting preserves the bounded constructible property.
Source: the paragraph "Forgetful functor and Frobenius" of the current definition.
Proof: exact forgetting preserves cohomology and boundedness. Its cohomology comparison
identifies each forgotten Weil cohomology module with the underlying cohomology sheaf;
transport constructibility across that isomorphism.
(blueprint: def-weil-weil-sheaf-complex). -/
theorem condensedWeilForget_mem (K : condensedWeilComplex Λ g) :
    boundedConstructible (condensedRingObj Λ Y)
      ((condensedWeilModuleForget Λ g).mapDerivedCategory.obj K.obj) := by
  refine ⟨(condensedWeilModuleForget Λ g).bounded_mapDerivedCategory_obj K.property.1, ?_⟩
  intro n
  exact (K.property.2 n).of_iso
    (((condensedWeilModuleForget Λ g).mapDerivedCategoryHomologyFunctorIso n).app K.obj)

/-- The canonical functor For to bounded constructible condensed complexes.
Source: the paragraph "Forgetful functor and Frobenius" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
def condensedWeilForget : condensedWeilComplex Λ g ⥤
    (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory :=
  (boundedConstructible (condensedRingObj Λ Y)).lift
    ((condensedWeilComplexProperty Λ g).ι ⋙
      (condensedWeilModuleForget Λ g).mapDerivedCategory) (condensedWeilForget_mem Λ g)

/-- Derived Frobenius is the localization of the termwise structure isomorphisms.
Source: the paragraph "Forgetful functor and Frobenius" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
def condensedWeilDerivedStructure :
    (condensedWeilModuleForget Λ g).mapDerivedCategory ⋙
      (CondensedRing.upperStar Λ g).mapDerivedCategory ≅
        (condensedWeilModuleForget Λ g).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (condensedWeilModuleForget Λ g)
    (CondensedRing.upperStar Λ g)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (CategoryTheory.Endofunctor.IsoAlgebra.strNatIso (CondensedRing.upperStar Λ g))

/-- Realization of derived Weil complexes as strict pairs. Its morphism map is exact
forgetting, and its structure is the derived termwise Weil isomorphism.
Source: the paragraph "Strict Weil complexes" of the current definition
(blueprint: def-weil-weil-sheaf-complex). -/
def condensedWeilRealization : condensedWeilComplex Λ g ⥤ condensedStrictWeilComplex Λ g where
  obj K := ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((condensedWeilModuleForget Λ g).mapDerivedCategory.obj K.obj)
    ((condensedWeilDerivedStructure Λ g).app K.obj), condensedWeilForget_mem Λ g K⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    { f := (condensedWeilModuleForget Λ g).mapDerivedCategory.map f.hom
      h := (condensedWeilDerivedStructure Λ g).hom.naturality f.hom })

section Derived

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ Y) [IsIso g]

end Derived

end WeilConjectures
