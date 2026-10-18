/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PicardGroup
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections

/-! # Units and Picard groups of the affine and punctured lines

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-affine-punctured-line-algebra; Stacks Project, Tags 03P4, 01HV, 0BCH and 01IB
(blueprint: lem-pur-affine-punctured-line-algebra).

The unit groups below are the actual values of the small etale unit sheaf at the terminal
object. Multiplicative notation reverses the additive convention of gmSheaf; ULift is retained.
The two summands of the cokernel are written as a product, their finite direct sum.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffinePuncturedLine

/-- Global sections of the existing etale unit sheaf on Spec R, in multiplicative notation.
Source: Stacks, Tag 03P4 (2) (blueprint: lem-pur-affine-punctured-line-algebra). -/
abbrev specUnits (R : Type u) [CommRing R] :=
  Multiplicative ((Spec (CommRingCat.of R)).gmSheaf.obj.obj
    (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of R))))))

/-- A coordinate-ring unit as the corresponding actual global etale unit section.
This is the canonical Gamma(Spec R) identification, followed by the unit-sheaf type tags.
Source: Stacks, Tags 01HV (1) and 03P4 (2)
(blueprint: lem-pur-affine-punctured-line-algebra). -/
def specUnitSection (R : Type u) [CommRing R] (a : Rˣ) : specUnits R :=
  Multiplicative.ofAdd (ULift.up (Additive.ofMul
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom a)))

/-- The Laurent monomial a*t^n as a unit, with its specified inverse.
Source: blueprint lem-pur-affine-punctured-line-algebra, Laurent-unit computation
(blueprint: lem-pur-affine-punctured-line-algebra). -/
def laurentUnit (k : Type u) [Field k] (a : kˣ) (n : ℤ) : (LaurentPolynomial k)ˣ :=
  Units.map LaurentPolynomial.C.toMonoidHom a * (LaurentPolynomial.isUnit_T n).unit

/-- The canonical unit descriptions, the two Picard vanishings and the power-map cokernel.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-affine-punctured-line-algebra; Stacks, Tags 03P4, 01HV, 0BCH and 01IB
(blueprint: lem-pur-affine-punctured-line-algebra).

Proof:
1. By the defining value of gmSheaf at the terminal etale object, its global sections are
   Gamma(X, O_X)^units. GammaSpecIso identifies this group on Spec R with R^units.
2. If two nonzero polynomials multiply to one, their degrees add to zero. Both are constant;
   conversely every nonzero scalar is a unit [def-weil-field, def-weil-polynomial-ring].
3. For Laurent polynomials, the least and greatest nonzero exponents add under multiplication.
   If uv=1, their two widths add to zero, so both widths vanish. Thus each unit has a unique
   expression a*t^n, and its inverse is a^(-1)*t^(-n) [def-weil-laurent-polynomial-ring].
4. The polynomial ring is a PID [lem-pur-polynomial-field-pid]. For a Laurent ideal J, contract
   to k[T], choose its generator g, and write each x in J as f/T^n. Then f=T^n*x belongs to
   the contracted ideal, hence x belongs to gB; conversely gB is contained in J. The extreme
   coefficient computation proves the Laurent ring is a domain, so it too is a PID.
5. For any invertible module sheaf L on either affine scheme, its section module M has
   bijective evaluation Hom(M,R) tensor M -> R [lem-sc-affine-invertible-sections]. Over the
   PIDs in step 4 it is isomorphic to R [lem-pur-pid-invertible-module-trivial].
6. Invertible sheaves are quasi-coherent [def-sc-invertible-module]. Apply the affine tilde/
   Gamma functor and its quasi-coherent counit to the section-module isomorphism from step 5
   [lem-weil-pbc-affine-tilde-gamma-adjunction]. It gives L isomorphic to O_X, the identity
   Picard class [def-sc-picard-group]. This works over any field, without algebraic closure.
7. In the unique coordinates (a,n), the N-th power map is (a,n) -> (a^N,N*n). The map taking
   a*t^n to ([a],[n]) is surjective, with kernel precisely the N-th powers. The inverse on
   quotient classes sends ([a],[n]) to [a*t^n]; changing representatives multiplies this by
   an N-th power, so it is well defined. This gives the specified group isomorphism.
8. When every scalar unit is an N-th power, the scalar quotient vanishes. The remaining
   Z/N is generated by [1], hence by the class of t. The scalar assumption is precisely
   surjectivity of its power map. For algebraically closed k a root of X^N-a is nonzero
   whenever a is nonzero. For N=1 the quotient and its distinguished generator are trivial.
   The characteristic restriction is retained, though the algebra works without it. -/
theorem affine_punctured_line_algebra (k : Type u) [Field k] :
    Function.Bijective (fun a : kˣ ↦
      specUnitSection (Polynomial k) (Units.map Polynomial.C.toMonoidHom a)) ∧
    Function.Bijective (fun p : kˣ × ℤ ↦
      specUnitSection (LaurentPolynomial k) (laurentUnit k p.1 p.2)) ∧
    Subsingleton (Spec (CommRingCat.of (Polynomial k))).Pic ∧
    Subsingleton (Spec (CommRingCat.of (LaurentPolynomial k))).Pic ∧
    (∀ (N : ℕ), 1 ≤ N → IsUnit (N : k) →
      (∃ e :
          (specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range) ≃*
            ((kˣ ⧸ (powMonoidHom N).range) × Multiplicative (ZMod N)),
        ∀ (a : kˣ) (n : ℤ),
          e (QuotientGroup.mk (specUnitSection (LaurentPolynomial k) (laurentUnit k a n))) =
            (QuotientGroup.mk a, Multiplicative.ofAdd (n : ZMod N))) ∧
      ((∀ a : kˣ, ∃ b : kˣ, b ^ N = a) →
        (∀ x : specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range,
          ∃ n : ℤ, x =
            (QuotientGroup.mk
              (specUnitSection (LaurentPolynomial k) (laurentUnit k 1 1))) ^ n) ∧
        Function.Surjective (fun a : kˣ ↦ a ^ N)) ∧
      (IsAlgClosed k → ∀ a : kˣ, ∃ b : kˣ, b ^ N = a)) := by
  sorry

end AlgebraicGeometry.AffinePuncturedLine
