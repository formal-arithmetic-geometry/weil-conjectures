/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSmallGeneratorSections
import WeilConjectures.AlgebraicGeometry.EtaleSmallGeneratorSeparating
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties

/-! Small-valued test objects for injectivity on the small étale site. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Injectivity can be tested on extensions into objectwise small sheaves.
Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO;
small affine site construction in Mathlib.AlgebraicGeometry.Sites.AffineEtale. -/
theorem etale_injective_of_small_extensions (X : Scheme.{u})
    (T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hT : ∀ {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}},
      (∀ U : X.Etaleᵒᵖ, Small.{u} (B.obj.obj U)) →
      ∀ (f : A ⟶ B) [Mono f] (g : A ⟶ T), ∃ h : B ⟶ T, f ≫ h = g) :
    Injective T := by
  let G := etaleSmallGenerator X
  have hG : IsSeparator G := etaleSmallGenerator_isSeparator X
  have hsmall : ∀ U : X.Etaleᵒᵖ, Small.{u} (G.obj.obj U) :=
    etaleSmallGenerator_sections_small X
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp.{u + 1} hG]
  intro A B f hf
  cases hf with
  | mk M =>
    constructor
    intro a b sq
    obtain ⟨h, hh⟩ := hT hsmall M.arrow a
    exact ⟨⟨{ l := h, fac_left := hh, fac_right := (isZero_zero _).eq_of_tgt _ _ }⟩⟩

end AlgebraicGeometry.Scheme
