/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base change of an indexed coproduct of copies of a scheme

Source: literature/stacks-project/schemes.tex, Tags 01JB and 01JC; Section 26.17
(blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-base-change)
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/--
Base change preserves an indexed coproduct of copies of a scheme.

Source: literature/stacks-project/schemes.tex, Tags 01JB and 01JC; Section 26.17
(blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-base-change).
Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, coprojections are open immersions
   with pairwise disjoint images covering the coproduct. Use `def-pc-fibre-product`
   to form the maps with projections identity and v followed by the coprojection;
   assemble them using `Sigma.desc`.
2. By `lem-weil-pbc-open-fibre-product`, the inverse image of each summand is an
   open subscheme isomorphic to V. These opens are disjoint and cover the pullback.
   By `lem-weil-pbc-scheme-morphism-gluing`, glue their inverse maps into the
   coproduct of copies of V. Both composites are identities by uniqueness of
   coproduct maps and gluing. The displayed restriction formula identifies each
   coprojection with its base change.
-/
theorem baseChange_sigmaScheme_iso
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :
    IsIso (Sigma.desc (fun e ↦
      pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp))) ∧
      ∀ e : E,
        Sigma.ι (fun _ : E ↦ V) e ≫
            Sigma.desc (fun e ↦
              pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp)) =
          pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp) := by
  sorry

end AlgebraicGeometry
