/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The localizing closure

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node definition-localizing-subcategory (blueprint: definition-localizing-subcategory).

The ambient category is the unbounded derived category of module objects on the
small pro-etale site.  The localizing closure is defined as the intersection of
all full replete triangulated subcategories containing the bounded constructible
finite-Tor objects and closed under coproducts.  The definition is purely an
intersection and imposes no derived-completeness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A property describes a full replete triangulated subcategory closed under
all coproducts that exist in the ambient category.

Source: blueprint definition-localizing-subcategory, first paragraph
(blueprint: definition-localizing-subcategory). -/
def IsLocalizingSubcategory {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
    ∀ {I : Type u} (F : Discrete I ⥤ C), (hF : HasColimit F) →
      (∀ i : I, P (F.obj (Discrete.mk i))) →
        let _ := hF
        P (colimit F)

/-- The intersection of all localizing subcategories containing `S`.

Source: blueprint definition-localizing-subcategory, first paragraph
(blueprint: definition-localizing-subcategory). -/
def localizingClosure {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : ObjectProperty C :=
  fun K => ∀ P : ObjectProperty C, IsLocalizingSubcategory P →
    (∀ L : C, S L → P L) → P K

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

/-- The localizing closure of bounded constructible finite-Tor complexes on a
pro-etale scheme.

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node definition-localizing-subcategory (blueprint: definition-localizing-subcategory).
The coefficient ring is the condensed ring `Λ`; `condensedRingObj Λ X` is its
pullback `Λ_X`, and `ConstantModelConstructibleFiniteTor Λ X` is `Dctf(X, Λ)`.
The localizing closure is the intersection defining the smallest full replete
triangulated subcategory closed under all ambient coproducts; no completeness
condition is imposed.
-/
noncomputable def localizingClosureProEtale
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K)

end AlgebraicGeometry.ProEtale
