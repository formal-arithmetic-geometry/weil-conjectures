/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.ClosedImmersionProducts

/-!
# Clopen pieces and their affine lines are separated of finite type

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-inv/
`prop-pur-a1-invariance.md`, Proof Step 1 (blueprint: lem-pur-clopen-affine-line-finite-type).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- A clopen open subscheme of a separated finite-type scheme over a field, and each
relative affine space over it, are separated and of finite type over that field.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-inv/
`prop-pur-a1-invariance.md`, Proof Step 1 (blueprint: lem-pur-clopen-affine-line-finite-type).

Proof:
1. For every affine open V of Y, the inverse image under j is U ∩ V, using
   `def-weil-open-immersion`. It is closed in V by hU, and V is quasi-compact by
   `lem-weil-pbc-affine-scheme-qcqs`. The node `lem-weil-pbc-closed-in-quasi-compact`
   makes this inverse image quasi-compact. Thus j is quasi-compact by
   `def-weil-finite-type-morphism`.
2. Apply `lem-weil-pbc-qc-open-immersion-finite-type` to j, and then compose with f
   using `lem-sfb-finite-type-composition-base-change`(1). This gives finite type
   for the restricted structure morphism j ≫ f.
3. The diagonal of U over Spec k is the base change of the diagonal of Y along
   j × j: the pullback identifies with U because j is a monomorphism by
   `lem-weil-pbc-open-immersion-monomorphism`, using `def-pc-fibre-product`.
   Separatedness of f and `def-weil-proper-morphism` make its diagonal a closed
   immersion. Apply `lem-weil-pbc-closed-immersion-base-change` to obtain
   separatedness of j ≫ f.
4. Write X = A^r_U and p : X ⟶ U. By `def-sbc-affine-space`, over an affine open
   Spec R of U the projection is Spec R[t₁, …, tᵣ] ⟶ Spec R. Hence p is affine
   by `pqf-def-affine-morphism`. The variables generate the polynomial algebra,
   so these charts give local finite type by `def-weil-finite-type-morphism`.
   By `lem-weil-pbc-affine-morphism-permanence`(3), p is quasi-compact and
   separated. Thus p is of finite type.
5. Factor the diagonal of X over Spec k through X ×_U X. The second map
   X ×_U X ⟶ X ×_(Spec k) X is the base change of the diagonal of U along
   p × p, by the universal property in `def-pc-fibre-product`. Step 3 and
   `lem-weil-pbc-closed-immersion-base-change` make it a closed immersion.
   The first map is a closed immersion by Step 4 and `def-weil-proper-morphism`.
   Compose them using `lem-weil-pbc-closed-immersion-products` to obtain
   separatedness of the composite structure morphism of X.
6. Apply `lem-sfb-finite-type-composition-base-change`(1) to p and j ≫ f,
   using Steps 4 and 2, to get finite type for X over Spec k. Empty U is
   admitted throughout. For r = 0, `def-sbc-affine-space` identifies p with
   the identity up to its canonical isomorphism; no positive-rank hypothesis
   is used.
-/
theorem clopen_affine_space_separated_finite_type
    {k : Type u} [Field k] {Y U : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ Y) [IsOpenImmersion j] (hU : IsClosed (Set.range j.base)) :
    (IsSeparated (j ≫ f) ∧ LocallyOfFiniteType (j ≫ f) ∧ QuasiCompact (j ≫ f)) ∧
      ∀ r : ℕ,
        IsSeparated ((AffineSpace (ULift.{u} (Fin r)) U ↘ U) ≫ j ≫ f) ∧
          LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin r)) U ↘ U) ≫ j ≫ f) ∧
          QuasiCompact ((AffineSpace (ULift.{u} (Fin r)) U ↘ U) ≫ j ≫ f) := by
  sorry

end AlgebraicGeometry
