/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion
import WeilConjectures.RingTheory.QuasiFiniteFourRings

/-!
# Cancellation for local quasi-finiteness of scheme morphisms

Source: Stacks Project, Morphisms of Schemes, Tag 03WR,
`lemma-permanence-quasi-finite`, final assertion
(blueprint: lem-sfb-scheme-lqf-cancellation).

Local quasi-finiteness is `Scheme.Hom.IsLocallyQuasiFinite`, the predicate of Tag 01TD
including local finite type.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- If a composite of scheme morphisms is locally quasi-finite, then its first morphism
is locally quasi-finite, including the local finite-type condition. There is no
hypothesis on the second morphism and no quasi-compactness, separation, or Noetherian
hypothesis.

Source: Stacks Project, Morphisms of Schemes, Tag 03WR,
`lemma-permanence-quasi-finite`, final assertion
(blueprint: lem-sfb-scheme-lqf-cancellation).

Proof:
1. Fix `x` in `X`, put `y = f x` and `z = g y`. By
   `lem-weil-pbc-affine-opens-basis` (Tag 01IT), choose affine opens `W` containing `z`,
   `V` containing `y` inside the inverse image of `W`, and `U` containing `x` inside
   the inverse image of `V`. Only continuity and the affine-open basis are used.
2. Set `A = Γ(Z, W)`, `B = Γ(Y, V)` and `C = Γ(X, U)`. By contravariant functoriality
   (`def-weil-affine-spectrum`), the composite of `A → B → C` is the section map
   for the restricted composite. Apply (1) implies (2) of
   `lem-a1-scheme-lqf-affine-criterion` (Tag 01TK): `A → C` is of finite type and
   quasi-finite at every prime of `C`.
3. For any prime `r` of `C`, apply `lem-weil-pbc-quasi-finite-four-rings` (Tag 00PN)
   with `R = A`, `S = S' = C`, `R' = B`, and the identity map `C → C`. The square
   commutes by step 2, and its generation condition holds since each `c` is `c * 1`.
   Both primes of `C` are `r`. It follows that `B → C` is of finite type and
   quasi-finite at `r`.
4. Take `r` to be the prime corresponding to `x` in `U`. These affine opens and
   step 3 are exactly the witnesses for `f.IsQuasiFiniteAtPoint x` in
   `pqf-def-quasifinite` (Tag 01TD). Since `x` is arbitrary, `f.IsLocallyQuasiFinite`.
   For empty `X` the pointwise condition is vacuous.
-/
theorem isLocallyQuasiFinite_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : (f ≫ g).IsLocallyQuasiFinite) : f.IsLocallyQuasiFinite := by
  sorry

end AlgebraicGeometry.Scheme.Hom
