/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# An isolated fibre point becomes finite after elementary étale base change

Source: Stacks Project, More on Morphisms, Lemma 02LK, clauses (a), (b), (i)-(iii)
(blueprint: lem-weil-pbc-etale-local-finite-at-point-elementary).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Lemma 02LK, excluding its final persistence assertion
(blueprint: lem-weil-pbc-etale-local-finite-at-point-elementary).
An isolated fibre point of a locally finite type morphism admits an elementary étale
neighbourhood and a finite open piece with exactly one point over the distinguished base
point; that point lies over the original point with unchanged residue field.

Proof plan from the node:
1. Choose affine opens `x ∈ Y ⊆ X` and `f(Y) ⊆ W ⊆ S`, with `s ∈ W`, using
   `lem-weil-pbc-affine-open-spec-points`. The corresponding ring map `R → A` is finite type
   by `lem-weil-pbc-lft-affine-pairs`.
2. Use `f.fiberHomeo s` and the affine identifications to see that the prime corresponding
   to `x` is isolated among the primes of `A` over the prime corresponding to `s`.
3. Apply `lem-weil-pbc-etale-quasi-finite-finite-one-prime` (Stacks 00UJ) to obtain an étale
   algebra `R'`, a prime over `s` with unchanged residue field, and an idempotent `e` of
   `C = R' ⊗[R] A` whose localization is finite and has a unique prime over that base prime.
4. Put `U = Spec R'`. Its composite map to `W ⊆ S` is étale by
   `lem-weil-pbc-etale-ring-map-iff-etale-affine` and
   `lem-weil-pbc-etale-composition-cancellation`. The residue-field identifications of
   `lem-weil-pbc-spec-residue-field-identification` give the elementary neighbourhood.
5. The lemmas `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`
   and `lem-weil-pbc-principal-localization-open-immersion` identify `Spec Cₑ` with an open
   subscheme `V` of `X ×[S] U`, compatibly with both projections.
6. Apply `lem-weil-pbc-finite-local-on-target` to show `V → U` is finite.
7. The unique prime supplied in step 3 gives the unique point over `u` and maps to `x`.
8. Since `κ(s) → κ(u)` is an isomorphism, `κ(x) ⊗[κ(s)] κ(u)` is `κ(x)` and is a field.
   The lemmas `lem-weil-pbc-fibre-product-points` and
   `lem-weil-pbc-fibre-product-point-residue-field` identify its sole prime with the point
   just constructed and identify its residue field with `κ(v)`, compatibly with `κ(x)`.
   Hence the induced map `κ(x) → κ(v)` is an isomorphism. -/
theorem exists_etale_finite_open_of_isolated_fiber_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = f x ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (V : (pullback f φ).Opens), IsFinite (V.ι ≫ pullback.snd f φ) ∧
        ∃ (v : V), (V.ι ≫ pullback.snd f φ) v = u ∧
          (∀ (w : V), (V.ι ≫ pullback.snd f φ) w = u → w = v) ∧
          (V.ι ≫ pullback.fst f φ) v = x ∧
          IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v) := by
  sorry

end AlgebraicGeometry
