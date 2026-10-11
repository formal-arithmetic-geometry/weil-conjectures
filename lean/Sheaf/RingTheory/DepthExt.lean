/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Depth via Ext from the residue field

Source: Stacks Project, Algebra, Lemma 10.72.5 (Tag 00LW)
(blueprint: lem-weil-pbc-depth-ext).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Abelian

namespace IsLocalRing

/-- For a nonzero finite module over a Noetherian local ring, depth is the least degree
of nonzero Ext from the residue field (Stacks, Tag 00LW;
(blueprint: lem-weil-pbc-depth-ext)). The `ULift`s place the residue field and the module
in one universe without restricting either carrier; `ULift.moduleEquiv` identifies each
lift with the original module.

Proof:
1. Nakayama (lem-weil-pbc-nakayama-jacobson) gives `m M ≠ M`. The regular-sequence
   definition (def-weil-pbc-depth), the support-dimension bound
   (lem-weil-pbc-depth-le-support-dimension), and finite local dimension
   (lem-weil-pbc-noetherian-local-finite-krull-dimension) give finite depth `d`.
2. Ext in degree zero is Hom (lem-weil-pbc-ext-zero-hom). A nonzero map from the
   residue field corresponds to a nonzero element annihilated by `m`, so `m` is
   associated. The nonzerodivisor criterion
   (lem-weil-pbc-nonzerodivisor-if-maximal-not-associated) gives depth zero exactly
   when this Ext group is nonzero; for positive depth Ext in degree zero vanishes.
3. Choose the first element `x` of a maximal-length regular sequence
   (def-weil-pbc-regular-sequence). Its tail on `Q = M/xM` is regular, and every
   regular sequence on `Q` prepends with `x` to one on `M`, by the successive quotient
   identifications. Thus `Q` is nonzero finite and has depth `d-1`. Induct on depth.
4. Apply the long exact sequence (lem-weil-pbc-ext-long-exact-second-variable) to
   `0 → M → M → Q → 0`, whose first map is multiplication by `x`. Since `x` annihilates
   the residue field, all scalar maps on Ext vanish
   (lem-weil-pbc-ext-annihilator-first-variable). This gives short exact sequences
   `0 → Ext^j(κ,M) → Ext^j(κ,Q) → Ext^(j+1)(κ,M) → 0` for every `j ≥ 0`.
5. The inductive vanishing below `d-1` for `Q`, together with the degree-zero
   vanishing for `M`, gives vanishing below `d` for `M`. At degree `d-1` for `Q`,
   the first group is zero (also when `d=1`) and the middle group is nonzero,
   so Ext in degree `d` for `M` is nonzero. This proves existence and minimality. -/
theorem exists_depth_eq_ext_degree {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ i : ℕ, depth (R := R) M = (i : ℕ∞) ∧
      Nontrivial (Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R (ULift.{u} M)) i) ∧
      ∀ j : ℕ, j < i →
        Subsingleton (Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
          (ModuleCat.of R (ULift.{u} M)) j) := by
  sorry

end IsLocalRing
