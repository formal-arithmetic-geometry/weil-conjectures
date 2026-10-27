/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.FinitePrecoverage

/-!
# Left exact covering functors and left adjoints

Source: Stacks Project, Sites, Tags 00X6 and 03A1, with the restriction and transformation
formulation of lem-per-lex-cover-functor-extension
(blueprint: def-per-lex-cover-functor-categories).

Both categories are full subcategories of functor categories: every natural transformation
is an arrow. Joint epimorphy is expressed by right cancellation, including empty families.
-/

@[expose] public section

set_option autoImplicit false

universe w u v u₂ v₂

namespace CategoryTheory

open Limits

/-- Left exact functors carrying the generating finite coverings to jointly epimorphic
families. The right-cancellation formula includes an empty covering.
Source: Stacks Sites 00X6, 03A1, and the topos-valued extension formulation
(blueprint: def-per-lex-cover-functor-categories). -/
def lexCoverFunctorProperty {C : Type w} [SmallCategory C] (K : Precoverage C)
    (E : Type u) [Category.{v} E] : ObjectProperty (C ⥤ E) :=
  fun A ↦ PreservesFiniteLimits A ∧
    ∀ (U : C) (I : Type w) [Finite I] (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ K U →
      ∀ (G : E) (b c : A.obj U ⟶ G),
        (∀ i, A.map (f i) ≫ b = A.map (f i) ≫ c) → b = c

/-- Finite-limit-preserving left adjoints, with all natural transformations as arrows in
the associated full subcategory. Adjointness is a property, not a choice of adjunction.
Source: Stacks Sites 00X6, 00XA
(blueprint: def-per-lex-cover-functor-categories). -/
def lexLeftAdjointProperty (D : Type u) [Category.{v} D]
    (E : Type u₂) [Category.{v₂} E] : ObjectProperty (D ⥤ E) :=
  fun L ↦ PreservesFiniteLimits L ∧ L.IsLeftAdjoint

end CategoryTheory
