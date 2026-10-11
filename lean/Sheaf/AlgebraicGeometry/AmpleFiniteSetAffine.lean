/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Ample

/-! # Affine neighbourhoods of finite sets on schemes with an ample invertible module

Source: Stacks Project, Properties, Lemma 01ZY, case (3)
(blueprint: lem-sc-ample-finite-set-affine).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every finite subset of a scheme carrying an ample invertible module lies in an affine open.
Source: Stacks Project, Properties, Lemma 01ZY, case (3)
(blueprint: lem-sc-ample-finite-set-affine).

Proof:
1. By `lem-sc-ample-proj-open`, embed `X` as an open subscheme of `Proj S`
   (`def-pc-proj`). Its boundary `T`, the closure of `X` minus `X`, is closed.
2. By `lem-sc-proj-standard-open-basis`, choose finitely many positive-degree homogeneous
   elements whose standard opens cover `E` and avoid `T`.
3. Apply `lem-sc-graded-prime-avoidance` to their generated graded ideal and the finitely
   many point primes of `E`. Obtain a homogeneous positive-degree element `f` whose
   standard open contains `E` and is contained in the union of the selected standard opens.
4. The intersection `U` of `X` with this standard open is open and closed in that affine
   standard open. Its inclusion is a closed immersion (`def-weil-closed-immersion`): the
   structure-sheaf map is an isomorphism on `U` and has zero target on its open complement.
   A closed immersion is affine (`pqf-def-affine-morphism`), so `U` is affine and contains `E`.
-/
theorem exists_affineOpen_of_isAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (hL : Modules.IsAmple X L) (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := by
  sorry

end AlgebraicGeometry.Scheme
