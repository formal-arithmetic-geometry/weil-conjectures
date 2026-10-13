/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.PolynomialOriginRegularLocal
import Sheaf.RingTheory.FlatOverRegular

/-!
# Flatness of the polynomial-append closed-fibre map

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo,
property (1); Algebra, Tags 00OP and 07DY.
-/

@[expose] public section

open scoped TensorProduct
set_option autoImplicit false
universe u v
namespace Algebra

/-- The closed fibre of adjoining polynomial coordinates is flat on a target where
those coordinates form a regular sequence on the original closed fibre.
Source: Stacks Project, Tag 07FH, lemma-solution-modulo, property (1);
Algebra, Tags 00OP and 07DY.
(blueprint: lem-weil-pbc-flat-polynomial-append-tensor-fibre).

Proof: Write A₀ = k[X_j]_{p₀}, A₁ = k[X_j,Y_i]_{p₁}, and L = Λ_q.
Reduction by p₀ identifies A₁/m₀A₁ with κ(p₀)[Y_i] localized at its
origin ideal. Modulo q every new coordinate is zero. Polynomial evaluation therefore gives
p₁ = p₀P₁ + (Y_i): the constant-in-Y term is in the kernel exactly when its
coefficient lies in p₀. Inverting P₀ \ p₀ and reducing modulo p₀ leaves
κ(p₀)[Y_i] with contracted prime precisely (Y_i).
Localization and quotient universal properties give the canonical comparison,
carrying the variable images to the standard origin parameters. By Tag 00OP
the source fibre is regular local of dimension e, with these e generators of
its maximal ideal. Let S = L/p₀L. The induced local map from the source fibre
to S takes the origin parameters to the given regular sequence. The final
quotient is nonzero by regularity; thus S is a Noetherian local ring. Tag 07DY
makes this map flat. The quotient-tensor equivalence identifies
(A₁/m₀A₁) ⊗[A₁] L with S as modules over A₁/m₀A₁, since the localized
first-coordinate map is the composite of α and β. Transport the flatness
along that equivalence. For e = 0 the source fibre is κ(p₀) and flatness is
flatness over a field. No initial flatness, generation, or regular-local
hypothesis on S is used. The equality hc fixes the canonical inclusion map;
proof irrelevance makes its choice immaterial. -/
theorem flat_tensor_fibre_polynomial_append_of_regular_sequence
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime]
    (t e : ℕ) (xs : Fin t → Λ) (zs : Fin e → Λ)
    (hzq : ∀ i, zs i ∈ q)
    (hseq : RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp
          (MvPolynomial.aeval (R := k) xs).toRingHom))
      (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk
        ((q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp
            (MvPolynomial.aeval (R := k) xs).toRingHom))
        (algebraMap Λ (Localization.AtPrime q) (zs i))))) :
    let φ₀ : MvPolynomial (Fin t) k →ₐ[k] Λ := MvPolynomial.aeval xs
    let φ₁ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
      MvPolynomial.aeval (Fin.addCases xs zs)
    let ι : MvPolynomial (Fin t) k →+* MvPolynomial (Fin (t + e)) k :=
      (MvPolynomial.rename (Fin.castAdd e)).toRingHom
    let p₀ := q.comap φ₀.toRingHom
    let p₁ := q.comap φ₁.toRingHom
    ∀ hc : p₀ = p₁.comap ι,
      let α := Localization.localRingHom p₀ p₁ ι hc
      let β := Localization.localRingHom p₁ q φ₁.toRingHom rfl
      letI : Algebra (Localization.AtPrime p₀) (Localization.AtPrime p₁) := α.toAlgebra
      letI : Algebra (Localization.AtPrime p₁) (Localization.AtPrime q) := β.toAlgebra
      let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p₀)).map α
      Module.Flat (Localization.AtPrime p₁ ⧸ J)
        ((Localization.AtPrime p₁ ⧸ J) ⊗[Localization.AtPrime p₁]
          Localization.AtPrime q) := by sorry

end Algebra
