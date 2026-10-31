/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDgModules

/-! Conservativity and the derived counit for a quasi-isomorphism of sheaf dg algebras.

Source: Stacks Project, sdga.tex, Tag 0FTZ (the roof and triangle argument).
(blueprint: lem-sf-sheaf-dg-quasiiso-counit-is-iso).

The proof uses cohomology sheaves to show that restriction reflects localized
isomorphisms, then applies the adjunction triangle identity to the unit theorem. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The normalized derived counit is invertible for a quasi-isomorphism of dg algebras.
Source: Stacks Project, sdga.tex, Tag 0FTZ
(blueprint: lem-sf-sheaf-dg-quasiiso-counit-is-iso).

Proof: restriction preserves the underlying complex and hence reflects isomorphisms
by the cohomology-functor characterization of the saturated localization. Apply
the triangle identity to the already invertible unit and transport the resulting
isomorphism back across this conservative restriction. -/
theorem sheaf_dg_quasiiso_counit_isIso {A B : Algebra O} (α : A ⟶ B)
    (s : ScalarSystem α) (hα : QuasiIso α.hom) :
    letI := s.source
    letI := s.target
    ∀ N : Derived B, IsIso (s.model.adjunction.counit.app N) := by
  sorry

end CategoryTheory.RingedSiteDg
