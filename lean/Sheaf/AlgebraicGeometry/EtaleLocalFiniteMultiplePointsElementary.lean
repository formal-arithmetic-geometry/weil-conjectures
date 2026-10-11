/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finitely many isolated fibre points become finite pieces after an elementary étale base change

Source: Stacks Project, More on Morphisms, Lemma 02LL, lines 11974--12011.
(blueprint: lem-weil-pbc-etale-local-finite-multiple-points-elementary)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finitely many isolated points of a fibre become finite pieces after an elementary étale
base change. Source: Stacks Project, More on Morphisms, Lemma 02LL, lines 11974--12011
(blueprint: lem-weil-pbc-etale-local-finite-multiple-points-elementary).

Proof (the six steps of the node, following Stacks 02LL):
1. Induct on `n`. For `n = 0`, take `U = S`, the identity and `u = s`, with no opens.
   The identity is an open immersion (`def-weil-open-immersion`), hence étale by
   `lem-weil-pbc-etale-composition-cancellation`, and its residue-field map is the identity
   (`def-weil-residue-field`). For the step, retain the neighbourhood and opens for `n - 1`.
2. The points above `(x n, u)` correspond to primes of `κ(x n) ⊗[κ(s)] κ(u)` by
   `lem-weil-pbc-fibre-product-points`. Since `κ(s) → κ(u)` is an isomorphism, this tensor
   product is `κ(x n)`, a field with one prime. Thus there is a unique point `x'_n`.
   By `lem-weil-pbc-fibre-product-point-residue-field`, its residue field is `κ(x n)`
   compatibly with the first projection.
3. The second projection is locally of finite type by `lem-weil-pbc-lft-base-change`.
   The point `x'_n` lies over `u` and is isolated in that fibre by
   `lem-weil-pbc-isolated-fibre-point-base-change` (`def-pc-scheme-fibre`).
4. Apply `lem-weil-pbc-etale-local-finite-at-point-elementary` (Stacks 02LK) to obtain
   `(U', u') → (U, u)` and a finite open `V_n` with the unique-point and residue-field
   properties. Identify the iterated fibre product with `X ×[S] U'` using
   `lem-weil-pbc-cartesian-square-pasting` (`def-pc-fibre-product`). Compose the étale
   neighbourhoods using `lem-weil-pbc-etale-composition-cancellation`; the composite maps
   `u'` to `s`, and its residue-field map is the composite of two isomorphisms.
5. For the last open, the first projection sends its unique point to `x'_n` and then to
   `x n`. Its residue-field map is the composite of the isomorphisms from steps 2 and 4
   (`def-weil-residue-field`), so this open satisfies all three clauses for `x n`.
6. Pull back each earlier open along `X ×[S] U' → X ×[S] U`. By
   `lem-weil-pbc-elementary-etale-finite-piece-persistence` (the final assertion of 02LK),
   each remains finite with a unique point above `u'` projecting to its original `x i`
   with unchanged residue field. These opens together with `V_n` complete the induction.
-/
theorem exists_etale_local_finite_multiple_points_elementary
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hisolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = s ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (V : Fin n → (pullback f φ).Opens) (v : (i : Fin n) → (V i).toScheme),
        ∀ i : Fin n,
          IsFinite ((V i).ι ≫ pullback.snd f φ) ∧
          ((V i).ι ≫ pullback.snd f φ) (v i) = u ∧
          (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd f φ) w = u → w = v i) ∧
          ((V i).ι ≫ pullback.fst f φ) (v i) = x i ∧
          IsIso (((V i).ι ≫ pullback.fst f φ).residueFieldMap (v i)) := by
  sorry

end AlgebraicGeometry
