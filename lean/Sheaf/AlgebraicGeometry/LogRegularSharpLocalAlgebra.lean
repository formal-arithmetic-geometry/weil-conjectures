/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.Algebra.AffineMonoid.Irreducible
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Local algebra supplied by a sharp log regular chart

Source: ILO VI 1.2 and 1.6, pp. 69--70, VIII 3.4.1--3.4.3, p. 110.
(blueprint: lem-trf-log-regular-sharp-local-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.FineSaturatedLogScheme

/-- The actual strict henselization at a geometric point has a sharp characteristic
chart satisfying the hypotheses of the monoidal local regularity criterion. This only
prepares its local algebra; it asserts neither regularity of the ambient ring nor freeness
of the characteristic.

Source: ILO VI 1.2 and 1.6, pp. 69--70; VIII 3.4.1--3.4.3, p. 110.
(blueprint: lem-trf-log-regular-sharp-local-algebra).

Proof:
Choose the pointed affine sharp chart from `exists_sharp_chart_of_logRegular` and
compose its germ and structural map with the canonical strict-local colimit comparison.
Write P for the additive characteristic. Sharpness identifies its nonzero elements with
the nonunit chart monomials; the log unit condition makes their images lie in the maximal
ideal. Every log-stalk element is a chart monomial times a unit, by the stalk-chart
pushout surjectivity. Thus the extension of the nonunit log ideal is precisely the ideal I
of nonzero chart monomials. The monoidal ideal contraction theorem gives the displayed
contraction property, including for the empty ideal.
Choose the relative separable closure K of the ordinary residue field in the geometric
field. The affine strict-local comparison and the pointed etale triples presentation
identify the prescribed colimit A with the strict henselization of the ordinary stalk R,
with its R-algebra structure. The ordinary stalk is Noetherian by local Noetherianity;
strict henselization is local and Noetherian. The proper ideal I gives a nonzero local
quotient. Transport the regular quotient and dimension formula of log regularity along
the colimit isomorphism to obtain the final two assertions.
Finite generation of P makes its group completion a finitely generated abelian group,
so its rationalization is finite dimensional. Set r equal to that dimension. The
additive group completion and the additive version of the multiplicative group completion
are canonically isomorphic, identifying r with the characteristic rank in the log
regularity formula. If P is N^s, its group completion is Z^s and its rationalization Q^s,
so r = s. This also proves the assertion when s = 0; no nonempty list is assumed. -/
theorem logRegular_sharp_local_algebra
    (X : FineSaturatedLogScheme.{u}) (hlog : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    let R := X.scheme.presheaf.stalk (Scheme.SpecToEquivOfField Ω X.scheme t).1
    let A := Scheme.strictHenselizationRing t
    let P := Additive (X.logStructure.characteristic t)
    IsFineSaturatedMonoid (Multiplicative P) ∧
      (∀ p : P, IsAddUnit p → p = 0) ∧
      ∃ (K : Type u) (_ : Field K)
        (_ : Algebra (IsLocalRing.ResidueField R) K)
        (_ : IsSepClosure (IsLocalRing.ResidueField R) K)
        (_ : Algebra R K) (_ : IsScalarTower R (IsLocalRing.ResidueField R) K)
        (_ : Algebra R A) (_ : IsLocalRing A) (_ : IsNoetherianRing A),
        Algebra.IsStrictHenselization R K A ∧
        ∃ (a : Multiplicative P →* A) (I : Ideal A) (r : ℕ),
          (∀ p : P, p ≠ 0 → a (Multiplicative.ofAdd p) ∈ IsLocalRing.maximalIdeal A) ∧
          (∀ J : Set P, (∀ p ∈ J, ∀ q : P, p + q ∈ J) →
            ∀ p : P, a (Multiplicative.ofAdd p) ∈
              Ideal.span ((fun q : P ↦ a (Multiplicative.ofAdd q)) '' J) ↔ p ∈ J) ∧
          I = Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' {p | p ≠ 0}) ∧
          r = Module.finrank ℚ (ℚ ⊗[ℤ] Algebra.GrothendieckAddGroup P) ∧
          (∀ s : ℕ, Nonempty (P ≃+ (Fin s → ℕ)) → r = s) ∧
          IsRegularLocalRing (A ⧸ I) ∧
          ringKrullDim A = ringKrullDim (A ⧸ I) + (r : WithBot ℕ∞) := by sorry

end AlgebraicGeometry.FineSaturatedLogScheme
