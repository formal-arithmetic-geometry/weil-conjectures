module
public import Mathlib.Algebra.Polynomial.Basic
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.FormallySmoothCompleteLocalRegular
import Sheaf.RingTheory.HypersurfaceDerivationRegular
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.PolynomialLocalCompletionFormallySmooth
@[expose] public section
universe u
namespace Polynomial
/-- Noetherianity component of the formal-fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PU.
(blueprint: lem-weil-pbc-another-helper-g-ring-noetherian-component)
Proof: localize the polynomial ring at the given maximal ideal, apply the
Noetherianity theorem for adic completions, and then apply the theorem that a
fibre of a Noetherian ring is Noetherian. -/
theorem formalFiber_isNoetherian (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing (r.Fiber C) := by sorry
end Polynomial
