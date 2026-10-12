module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dehomogenization equivalence for weak Popescu delocalization

Source: Stacks Project, proof of Tag 07F9, the final displayed isomorphism.
(blueprint: lem-weil-pbc-popescu-delocalize-dehomogenization-equiv)
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

/-- Source: Stacks Project, proof of Tag 07F9, the isomorphism following the
construction of B and b.
(blueprint: lem-weil-pbc-popescu-delocalize-dehomogenization-equiv)

Proof: Denote the right-hand quotient by D and its localization by C. Both
localizations invert the class of x₀*w*∏sⱼ, hence x₀, w and all sⱼ are units.
Define the polynomial map to C fixing x₀, the first n original variables and w,
and sending each of the last m original variables Xᵢ to xᵢ*w. Expanding the
support sum in hF gives Fⱼ(u,v*w,w) = w^(dⱼ)*fⱼ(u,v): in each monomial the
w-exponent is the sum of the last m exponents plus its complementary exponent;
hdegree ensures this sum is dⱼ. Thus x₀*Fⱼ maps to zero. The membership hg gives
sⱼ₊₁*gⱼ = 0 in D and hence gⱼ = 0 in C by the unit sⱼ₊₁. This map factors
through B and extends to B_b, since b maps to a unit.

Conversely map D to B_b by fixing x₀, the first n original variables and w, and
sending each remaining xᵢ to Xᵢ/w. The same identity gives fⱼ = w^(-dⱼ)*Fⱼ
under this substitution. In B_b, x₀*Fⱼ = 0 and x₀ is a unit, so Fⱼ = 0.
The map therefore descends to D and extends to C because x₀*w*∏sⱼ is a unit.
The composites fix the coefficients and every variable: the only nontrivial
identities are (xᵢ*w)/w = xᵢ and (Xᵢ/w)*w = Xᵢ. Polynomial and quotient
extensionality, followed by uniqueness of maps out of each localization, show
that these maps are inverse R-algebra maps. This also covers m=0, c=0, t=0,
and zero localizations. No Jacobian hypothesis is needed for this isomorphism. -/
theorem popescu_delocalize_dehomogenization_equiv_exists
    (R : Type u) [CommRing R]
    (n m c t : ℕ)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (g : Fin t → MvPolynomial (Fin n) R)
    (s : Fin (t + 1) → R)
    (hg : ∀ j : Fin t,
      C (s j.succ) * rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈
        Ideal.span (Set.range f))
    (d : Fin c → ℕ)
    (hdegree : ∀ j : Fin c, ∀ e ∈ (f j).support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j)
    (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
    (hF : ∀ j : Fin c, F j =
      ∑ e ∈ (f j).support,
        C ((f j).coeff e) *
          (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
          X (Fin.last (n + m + 1)) ^
            (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) :
    Nonempty (Localization.Away
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun j : Fin t =>
            rename (fun i : Fin n =>
              (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) ∪
            Set.range (fun j : Fin c => X (0 : Fin (n + m + 2)) * F j)))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
          C (∏ j : Fin (t + 1), s j))) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun j : Fin c =>
          rename (fun i : Fin (n + m) => i.castSucc.succ) (f j))))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1))
          * C (∏ j : Fin (t + 1), s j)))) := by
  sorry

end Algebra
