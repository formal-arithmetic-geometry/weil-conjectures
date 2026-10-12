/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum
import Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import Sheaf.RingTheory.PresentationsHomotopyEquivalent

/-!
# Conormal modules under principal localization

Source: Stacks Project, Algebra, Lemma 00S6 (lemma-conormal-module-localize)
(blueprint: lem-weil-pbc-conormal-module-principal-localization).
-/

@[expose] public section

universe u v

namespace Algebra.Extension

/-- Stacks Project, Algebra, Lemma 00S6 (lemma-conormal-module-localize).
(blueprint: lem-weil-pbc-conormal-module-principal-localization)
The kernels of the two polynomial presentations give the conormal modules `I/I²` and `J/J²`.
Their scalar actions are the quotient actions supplied by `Extension.Cotangent.module`.

Proof plan, following the node's six steps:
1. Form `K = NL(α) ⊗[S] S_g` and `NL(β)`. The polynomial differential basis theorem
   (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables) identifies their degree-zero
   terms with free modules of ranks `n` and `m`. The localization-tensor comparison
   (lem-weil-pbc-localization-module-tensor) identifies `K₁` with `(I/I²)_g`.
2. Choose a lift of `g` along `α`. Adjoin a variable mapped to `1/g` to obtain `β'`.
   By lem-weil-pbc-principal-localization-naive-cotangent, its naive cotangent complex
   is isomorphic to `K` plus the complex `S_g → S_g` given by multiplication by `g`.
3. This extra summand is contractible: multiplication by `g⁻¹` is its contracting
   homotopy. Inclusion and projection give a homotopy equivalence between `K` and `NL(β')`.
4. By lem-weil-pbc-nl-presentations-homotopy-equivalent, `NL(β')` and `NL(β)` are
   homotopy equivalent, since they present the same algebra `S_g`.
5. Compose the chain maps. If `u,v` are the inclusion/projection maps, `φ,ψ` the
   presentation comparison maps, and `h,h',H` the homotopies, use `v₁ h u₀` on `K`
   and `h' + φ₁ H ψ₀` on `NL(β)` to verify both composite homotopy identities.
6. Apply lem-weil-pbc-two-term-homotopy-equivalence-direct-sum to obtain
   `K₁ ⊕ NL(β)₀ ≅ NL(β)₁ ⊕ K₀`, and substitute the identifications of step 1.
-/
theorem conormalModule_principalLocalization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (g : S) (n m : ℕ)
    (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin m) R →ₐ[R] Localization.Away g)
    (hβ : Function.Surjective β) :
    Nonempty
      ((LocalizedModule.Away g (ofSurjective α hα).Cotangent ×
          (Fin m → Localization.Away g)) ≃ₗ[Localization.Away g]
        ((ofSurjective β hβ).Cotangent × (Fin n → Localization.Away g))) := by
  sorry

end Algebra.Extension
