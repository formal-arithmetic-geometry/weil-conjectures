/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDgModules

/-! The derived unit for a quasi-isomorphism of sheaf dg algebras.

Source: Stacks Project, sdga.tex, Tag 0FTZ (the good-resolution unit argument).
(blueprint: lem-sf-sheaf-dg-quasiiso-unit-is-iso).

The proof uses the cone of the algebra map, tensor-acyclicity of good right
modules, and the normalized derived-adjunction unit formula. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The normalized derived unit is invertible for a quasi-isomorphism of dg algebras.
Source: Stacks Project, sdga.tex, Tag 0FTZ
(blueprint: lem-sf-sheaf-dg-quasiiso-unit-is-iso).

Proof: resolve a module by a good right dg module. The cone of the algebra map
is acyclic, and tensor-acyclicity of the good resolution makes the tensor unit a
quasi-isomorphism. The normalized unit equation identifies this map with the
derived adjunction unit; naturality transports invertibility along the resolution. -/
theorem sheaf_dg_quasiiso_unit_isIso {A B : Algebra O} (α : A ⟶ B)
    (s : ScalarSystem α) (hα : QuasiIso α.hom) :
    letI := s.source
    letI := s.target
    ∀ M : Derived A, IsIso (s.model.adjunction.unit.app M) := by
  sorry

end CategoryTheory.RingedSiteDg
