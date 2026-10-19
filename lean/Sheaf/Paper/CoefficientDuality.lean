/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Artinian.Defs

/-! # Coefficient duality on the module derived category

Source: Weil blueprint, lem-weil-coefficient-frobenius, paragraphs 1--3;
Stacks Project, Tags 08J7 and 07VI (blueprint: def-sf-coefficient-duality).
The module category is the module category of the one-object ringed site.
Its natural small-Hom derived localization is supplied by its Grothendieck instance.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace WeilConjectures

/-- The full-subcategory predicate for bounded complexes with finite cohomology.
Finite means `Module.Finite`, including over infinite fields.
Source: blueprint lem-weil-coefficient-frobenius, first two clauses
(blueprint: def-sf-coefficient-duality). -/
def boundedFiniteCoefficientComplex (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ DerivedCategory.TStructure.t.bounded K ∧
    ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)

/-- Derived coefficient duality is internal Hom into the tensor unit `R[0]`.
The closed structure is the derived tensor--Hom adjunction, obtained by deriving
Hom into K-injective resolutions, as in the one-object case of Tag 08J7.
Source: blueprint lem-weil-coefficient-frobenius, first clause; Stacks 08J7
(blueprint: def-sf-coefficient-duality). -/
noncomputable def coefficientDerivedDual (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  MonoidalClosed.internalHom.flip.obj (𝟙_ (DerivedCategory (ModuleCat.{u} R)))

/-- Canonical derived evaluation: transpose evaluation after interchanging the
arguments by the Koszul braiding. No unspecified comparison or arbitrary map is chosen.
Source: blueprint lem-weil-coefficient-frobenius, displayed derived evaluation;
Stacks 07VI (blueprint: def-sf-coefficient-duality). -/
noncomputable def coefficientDerivedEvaluation {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    K ⟶ (ihom ((ihom K).obj (𝟙_ (DerivedCategory (ModuleCat.{u} R))))).obj
      (𝟙_ (DerivedCategory (ModuleCat.{u} R))) :=
  MonoidalClosed.curry
    ((DerivedMonoidal.braiding' (DerivedCategory.Qh (C := ModuleCat.{u} R))
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      ((ihom K).obj (𝟙_ (DerivedCategory (ModuleCat.{u} R)))) K).hom ≫
        (ihom.ev K).app (𝟙_ (DerivedCategory (ModuleCat.{u} R))))

/-- All finite-stage Frobenius-duality assertions packaged as a predicate, with no
self-injectivity assumption hidden in the derived dual's construction.
`IsArtinianRing` and self-injectivity together are the commutative quasi-Frobenius
convention. Exactness quantifies over all modules, not just finite modules.
The last clause identifies an equivalence with the actual derived coefficient dual
on the full bounded finite-cohomology subcategory, by a natural isomorphism.
Source: blueprint lem-weil-coefficient-frobenius, first clause; Stacks 0AVF
(blueprint: def-sf-coefficient-duality). -/
def coefficientFrobeniusProperties (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] : Prop :=
  Module.Injective.{u, u} R R ∧ IsArtinianRing R ∧
  (∀ (M N P : ModuleCat.{u} R) (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective g.dualMap ∧ Function.Exact g.dualMap f.dualMap ∧
        Function.Surjective f.dualMap) ∧
  (∀ M : ModuleCat.{u} R, Module.Finite R M →
    Module.Finite R (Module.Dual R M) ∧ Function.Bijective (Module.Dual.eval R M)) ∧
  ∃ F : (boundedFiniteCoefficientComplex R).FullSubcategoryᵒᵖ ⥤
      (boundedFiniteCoefficientComplex R).FullSubcategory,
    F.IsEquivalence ∧
      Nonempty (F ⋙ (boundedFiniteCoefficientComplex R).ι ≅
        (boundedFiniteCoefficientComplex R).ι.op ⋙ coefficientDerivedDual R)

end WeilConjectures
