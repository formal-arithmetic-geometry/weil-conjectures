/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finite-index enlargement of a lattice through a divisible subgroup

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, Lemma 3.6.4,
printed pages 252--253 (blueprint: lem-per-divisible-unit-lattice-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AddCommGroup

/-- A map from a finite free abelian group extends to a finite free enlargement that
surjects onto the torsion-free quotient by an `n`-divisible subgroup.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, Lemma 3.6.4,
printed pages 252--253 (blueprint: lem-per-divisible-unit-lattice-extension).

Proof: write `C = B / D`, `f = p.comp φ`, and `Q = C / f.range`. Induct strongly
on the positive finite cardinality of `Q`. If `Q` is trivial, take `G = L`, the identity
inclusion and `h = φ`; exponent zero suffices. Otherwise choose a nonzero class `q`
represented by `c = p b`. Its order `d` is at least two and divides `n`. Choose `a`
with `f a = d • c`, so `d • b - φ a` lies in `D`. Divisibility by `n`, and hence by
`d`, lets us adjust `b` inside its `D`-coset so that `d • b = φ a`.

If `d • x + k • a = 0`, torsion-freeness of `C` first implies `f x + k • c = 0`.
The order of `q` gives `k = d * t`; torsion-freeness of `L` then gives `x = -t • a`.
Conversely these pairs give all relations. Form the subgroup `L₁ = dL + ℤa` of `L`.
It is finite free by `lem-weil-subgroup-finite-free-abelian-group-free`, namely
`Submodule.basisOfPid` after choosing a finite basis of `L`. The map `j x = d • x`
is injective. Define `φ₁ (d • x + k • a) = φ x + k • b`; the relation calculation
and `d • b = φ a` prove well-definedness and additivity. Then `φ₁.comp j = φ`, and
`L₁ / j(L)` is killed by `d`, hence by `n`.

The image in `C` is `f(L) + ℤc`, so the new cokernel is `Q / ⟨q⟩`, of cardinality
`|Q| / d < |Q|`, still killed by `n`. Apply induction to `L₁, φ₁`. Compose its
injection `i₁` with `j`. If `n^s • g = i₁ y`, then `n • y` belongs to `j(L)`, so
`n^(s+1) • g` belongs to the composite image. The composite is injective, extends
`φ`, and still surjects onto `C`, as required. -/
theorem divisible_unit_lattice_extension
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : Type v) [AddCommGroup B] (D : AddSubgroup B) (φ : L →+ B)
    (hD : ∀ d : D, ∃ e : D, n • e = d)
    [IsAddTorsionFree (B ⧸ D)]
    [Finite ((B ⧸ D) ⧸ ((QuotientAddGroup.mk' D).comp φ).range)]
    (hQ : ∀ q : (B ⧸ D) ⧸ ((QuotientAddGroup.mk' D).comp φ).range, n • q = 0) :
    ∃ (G : Type u) (_ : AddCommGroup G),
      Module.Free ℤ G ∧ Module.Finite ℤ G ∧
      ∃ (i : L →+ G) (h : G →+ B),
        Function.Injective i ∧
        (∃ s : ℕ, ∀ q : G ⧸ i.range, n ^ s • q = 0) ∧
        h.comp i = φ ∧ Function.Surjective ((QuotientAddGroup.mk' D).comp h) := by
  sorry

end AddCommGroup
