/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact

/-! Independent-universe exactness interface for derived internal Hom.

Source: Stacks Project, Tag 08JC.
-/

@[expose] public section
set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C]

/-- Internal derived Hom is exact in both variables at independent universes.

Source: Stacks Project, Tag 08JC. -/
theorem ringedInternalHom_exact
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] :
    (∀ M : D.{c, v, r, w} J R,
      ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj M).CommShift ℤ,
        ((Functor.curry.obj
          (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj M).IsTriangulated) ∧
    (∀ K : D.{c, v, r, w} J R,
      ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op K)).CommShift ℤ,
        ((Functor.curry.obj
          (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op K)).IsTriangulated) := by
  constructor
  · intro M
    obtain ⟨S, hS, _⟩ := signedDerivedInternalHom_exact.{c, v, r, w} J R M
    exact ⟨S, hS⟩
  · intro K
    exact ⟨homCommShift.{c, v, r, w} J R K,
      hom_isTriangulated.{c, v, r, w} J R K⟩

end CategoryTheory.RingedHomUniverses
