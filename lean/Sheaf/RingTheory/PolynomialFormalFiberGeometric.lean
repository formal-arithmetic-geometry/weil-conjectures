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
/-- Geometric-regularity component of the formal-fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PU.
(blueprint: lem-weil-pbc-another-helper-g-ring-geometric-component)
Proof: after a finite purely inseparable residue-field extension, use the
completion finite-extension decomposition to write the base-changed fibre as a
finite product. Each factor is regular by the formally smooth completion and
derivation quotient lemmas, and a finite product of regular rings is regular;
this is precisely geometric regularity. -/
theorem formalFiber_isGeometricallyRegular_component (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C) := by sorry
end Polynomial
