/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleFiniteTypeReflection
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Finite-type reflection for the constant square-zero kernel

The missing geometric comparison is isolated here: constructibility of the constant
kernel on the chosen one-point pro-etale site forces finite type of its scalar module.
Source: the final paragraph of `det-def-sfb-bounded-constructible.proof.md` and
Stacks Project, Tag 093N (blueprint: lem-sfb-constant-kernel-finite-type-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- STATEMENT-DISPUTED: this declaration is false as stated; the zero module is constructible.
Constructibility of the constant square-zero kernel yields finite generation of its
scalar kernel.  The proof must identify a stratum with the whole separably closed point,
transport local finite presentations along a splitting of a pro-etale cover, and then apply
the constant-module finite-type reflection theorem.  These are the site-geometric steps
not present in Mathlib's abstract module API.
(blueprint: lem-sfb-constant-kernel-finite-type-reduction) -/
theorem constant_kernel_constructible_impossible
    {X : Scheme.{u}}
    {R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})}
    {K : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X}
    (hK : IsConstructibleModuleObject R.X K) : False := by
  sorry

end AlgebraicGeometry.ProEtale
