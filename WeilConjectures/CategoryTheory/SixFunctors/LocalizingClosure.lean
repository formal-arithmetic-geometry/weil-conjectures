/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure

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
all direct sums that exist in the ambient category: the sums indexed by a type of the
universe `v` of the morphisms, "arbitrary direct sums" in the notes meaning set-indexed sums
(Blueprint bot, Zulip #3571; as in Mathlib's `HasCoproducts.{v}`). It is the class
`CategoryTheory.ObjectProperty.IsLocalizing`
(`CategoryTheory.isLocalizingSubcategory_iff_isLocalizing`).

Source: blueprint definition-localizing-subcategory, first paragraph
(blueprint: definition-localizing-subcategory). -/
def IsLocalizingSubcategory {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
    ∀ {I : Type v} (F : Discrete I ⥤ C), (hF : HasColimit F) →
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

section Identification

variable {C : Type u} [Category.{v, u} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- `IsLocalizingSubcategory` is the class `CategoryTheory.ObjectProperty.IsLocalizing`: both
say triangulated, closed under isomorphisms and under the `v`-small direct sums that exist. -/
theorem isLocalizingSubcategory_iff_isLocalizing (P : ObjectProperty C) :
    IsLocalizingSubcategory P ↔ P.IsLocalizing := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact { toIsTriangulated := h₁
            toIsClosedUnderIsomorphisms := h₂
            isClosedUnderColimitsOfShape_discrete := fun J ↦
              ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
                rintro _ ⟨F, hF⟩
                exact h₃ F inferInstance fun i ↦ hF ⟨i⟩) }
  · intro h
    refine ⟨h.toIsTriangulated, h.toIsClosedUnderIsomorphisms, fun {I} F hF hFi ↦ ?_⟩
    have := h.isClosedUnderColimitsOfShape_discrete I
    exact P.prop_colimit F fun j ↦ hFi j.as

/-- `localizingClosure` is the localizing closure `CategoryTheory.ObjectProperty.localizingClosure`:
the intersection of the same family of properties. -/
theorem localizingClosure_eq_objectProperty (S : ObjectProperty C) :
    localizingClosure S = S.localizingClosure := by
  ext K
  constructor
  · intro hK Q hSQ hQ
    exact hK Q ((isLocalizingSubcategory_iff_isLocalizing Q).2 hQ) hSQ
  · intro hK P hP hSP
    exact hK P hSP ((isLocalizingSubcategory_iff_isLocalizing P).1 hP)

end Identification

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
