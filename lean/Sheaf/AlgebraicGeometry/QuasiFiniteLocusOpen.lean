/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Openness of the quasi-finite locus

Source: Stacks Project, Morphisms of Schemes, Tag 01TI
(blueprint: lem-sc-quasi-finite-points-open).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Hom

/-- The quasi-finite locus of a morphism is open, and the induced morphism on it is
locally quasi-finite (Stacks Project, Morphisms of Schemes, Tag 01TI).
(blueprint: lem-sc-quasi-finite-points-open)

Proof:
1. At a quasi-finite point `x`, choose affine opens `W = Spec(B)` containing `x` and
   `V = Spec(A)` containing `f(W)`, with `A → B` finite type and quasi-finite at the
   prime of `x`, by `pqf-def-quasifinite` (Stacks Tag 01TD, clause 1).
2. By `lem-weil-pbc-ring-quasi-finite-locus-open` (Stacks Tag 00QA), choose `g ∈ B`
   outside that prime such that `A → B_g` is quasi-finite at every prime.
3. The basic open `D(g)` is an affine open neighbourhood of `x` in `X`, by
   `lem-weil-pbc-affine-open-spec-points`, and maps into `V`. Its ring map `A → B_g`
   is finite type, since `B_g = B[1/g]`. Hence every point of `D(g)` is quasi-finite
   for `f`, by `pqf-def-quasifinite` (clause 1) and step 2.
4. The locus is the union of these open neighbourhoods, so is an open `U` of `X`.
5. For each point of `U`, its neighbourhood `D(g)` lies in `U`. The same affine
   neighbourhood and `V`, with the finite-type quasi-finite ring map `A → B_g`,
   witness quasi-finiteness of `U → S` at that point. Thus `U → S` is locally
   quasi-finite, by `pqf-def-quasifinite` (clause 2). -/
theorem isOpen_quasiFiniteAtPoint {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ U : X.Opens,
      (∀ x : X, x ∈ U ↔ IsQuasiFiniteAtPoint f x) ∧
        IsLocallyQuasiFinite (U.ι ≫ f) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
