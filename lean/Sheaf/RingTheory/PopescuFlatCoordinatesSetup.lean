module
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.GeometricallyRegularH1Injective
import Sheaf.RingTheory.LocalizationOfRegularRing
@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra
/-- The localized prime-power quotient has the Artinian-local and cotangent-finiteness
properties needed to apply the Popescu directed-subalgebra theorem.
(blueprint: lem-weil-pbc-popescu-flat-coordinates-setup)

Source: Stacks Project, Tag 07FH, first paragraph of the proof, and Tag 07E5.

Proof: Write L = Localization.AtPrime q and J = qL. Localization makes L Noetherian
and local with maximal ideal J. For every finite purely inseparable extension k'/k,
the algebra k' tensor L is the localization of k' tensor Λ at the image of Λ minus q.
Geometric regularity of Λ makes the latter regular; localization preserves regularity.
Thus L is geometrically regular. Since k is a field of characteristic p > 0, p is prime,
so Tag 07E5 applies and gives an injective K-linear map H1Cotangent k K into J/J²,
where K is the residue field of L. The ideal J is finitely generated because L is
Noetherian. The classes of any finite generating set span J/J² over K, so this space
is finite dimensional. An injective linear map into it makes H1Cotangent k K finite.

Because n ≥ 1, J^n is contained in the proper maximal ideal J and has radical J.
Consequently B = L/J^n is nonzero and local: the unique maximal ideal is the image of J.
It is Noetherian as a quotient of L. Every prime ideal of B pulls back to a prime of L
containing J^n, hence containing J, and must therefore pull back to J. Thus B has
Krull dimension zero and is Artinian by the Noetherian dimension-zero criterion.
The quotient map L → B followed by the residue map has kernel J. The third
isomorphism theorem therefore gives a k-algebra isomorphism from the residue field of B
to K. Functoriality of H1Cotangent along this isomorphism and its inverse gives inverse
semilinear maps on H1Cotangent; transport a finite K-generating set along these maps.
This proves the stated finiteness over the residue field of B. The existential witnesses
hArt and hLoc are proofs of properties of the already constructed quotient, not choices
of ring data. -/
theorem popescu_flat_coordinates_setup
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ hArt : IsArtinianRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
      ∃ hLoc : IsLocalRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
      IsLocalRing.maximalIdeal (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
        (q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) ∧
      Module.Finite (IsLocalRing.ResidueField
        (Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
        (H1Cotangent k (IsLocalRing.ResidueField
          (Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) := by
  sorry

end Algebra
