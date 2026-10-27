module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Sheaf.TraceFormula.ValuationClosedFibreNoetherian
import Sheaf.TraceFormula.ValuationFiniteModuleInjectivity
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization

/-! # Associated-prime specialization over a valuation domain

Source: Stacks Project, `more-morphisms.tex`, Tag 0GSI
(lemma-associated-point-specializes), third proof paragraph
(blueprint: lem-trf-valuation-associated-local-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Associatedness at the generic prime implies associatedness of the closed-fibre
maximal ideal when the closure has primary closed fibre.

Source: Stacks Project, Tag 0GSI (lemma-associated-point-specializes), third
proof paragraph (blueprint: lem-trf-valuation-associated-local-algebra).

The prime `qK` is the extension of `q` to `B ⊗[A] FractionRing A`. The action on
`N ⊗[A] FractionRing A` is transported from the ordinary base-change module
along tensor symmetry and cancellation, so `(b ⊗ k) • (n ⊗ l) = (b • n) ⊗ (k * l)`.
The localized action is Mathlib's canonical `LocalizedModule.moduleOfIsLocalization`.

Proof: the closed fibre is Noetherian by `valuation_closed_fibre_noetherian`,
and the reduction of a finite generating family generates its module. If its
maximal ideal were not associated, finiteness of associated primes and prime
avoidance would give `g ∈ q` avoiding all of them: the radical hypothesis
prevents any proper associated prime from containing the image of `q`. For an
empty associated-prime set take `g = 0`. The description of module zerodivisors
as the union of associated primes makes multiplication by `g` injective on the
closed fibre. Apply `valuation_finite_module_injectivity` to multiplication by
`g` on `N`; the target is flat over `A`, so this map is injective on `N`.
The fraction field is a flat localization, hence tensoring preserves this
injection. Localizing it at `qK` again preserves injectivity by the fraction
equality criterion. But `g` lies in the maximal ideal of the localized ring,
which by the generic associatedness hypothesis annihilates a nonzero element.
This contradicts injectivity and proves the conclusion. -/
theorem valuation_associated_local_algebra
    (A : Type u) (B : Type v) (N : Type w)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N]
    (q : Ideal B) [q.IsPrime]
    (h_zero : Ideal.comap (algebraMap A B) q = ⊥)
    (h_radical :
      (q ⊔ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)).radical =
        IsLocalRing.maximalIdeal B)
    (qK : Ideal (B ⊗[A] FractionRing A)) [qK.IsPrime]
    (hqK : qK = Ideal.map (algebraMap B (B ⊗[A] FractionRing A)) q)
    (h_generic :
      (fun [_tensor : Module (B ⊗[A] FractionRing A) (N ⊗[A] FractionRing A)] ↦
        @RingTheory.annihilatorAssociatedPrimes
          (Localization.AtPrime qK) _
          (LocalizedModule qK.primeCompl (N ⊗[A] FractionRing A)) _
          (LocalizedModule.moduleOfIsLocalization
            (S := qK.primeCompl) (T := Localization.AtPrime qK))
          (IsLocalRing.maximalIdeal (Localization.AtPrime qK)))
        (_tensor :=
          ((_root_.TensorProduct.comm B (B ⊗[A] FractionRing A) N).trans
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              A B B N (FractionRing A))).toAddEquiv.symm.module
                (B ⊗[A] FractionRing A))) :
    Ideal.map
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)))
        (IsLocalRing.maximalIdeal B) ∈
      RingTheory.annihilatorAssociatedPrimes
        (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
        (N ⧸ ((Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) •
          (⊤ : Submodule B N))) := by
  sorry

end Algebra
