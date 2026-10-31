/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Noetherianity and finite presentation on the closed fibre

Source: Stacks Project, `more-morphisms.tex`, Tag 0GSG (lemma-mod-injective-valuation-ring),
proof, second paragraph (blueprint: lem-trf-valuation-closed-fibre-noetherian).

## Main statement

The closed fibre of a local essentially finite type algebra over a valuation ring is
Noetherian, and reductions of finite modules are finitely presented over that fibre.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w

namespace Algebra

/--
The closed fibre of a local essentially finite type algebra over a valuation ring is
Noetherian, and every finite module has finitely presented reduction.

Source: Stacks Project, `more-morphisms.tex`, Tag 0GSG (lemma-mod-injective-valuation-ring),
proof, second paragraph (blueprint: lem-trf-valuation-closed-fibre-noetherian).

Proof steps: choose a finite type algebra and a multiplicative set presenting the
essentially finite type algebra; reduce modulo the maximal ideal of the valuation
ring and verify the induced localization by fractions; apply Noetherianity of finite
type algebras and its localization permanence; then reduce a finite generating family
of the module and apply finite-module finite-presentation over a Noetherian ring.
-/
theorem valuation_closed_fibre_noetherian
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [IsLocalHom (algebraMap A B)] :
    IsNoetherianRing
        (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ∧
      ∀ (N : Type w) [AddCommGroup N] [Module B N] [Module.Finite B N],
        Module.FinitePresentation
          (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
          (N ⧸ ((Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) •
            (⊤ : Submodule B N))) := by
  sorry

end Algebra

end
