/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import Sheaf.RingTheory.PolynomialAlgebraCohenMacaulay
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Rational-field tensors and their Cohen–Macaulay local rings

Source: Stacks Project, Algebra, Tag 045M (lemma-tensor-fields-CM), last two sentences
of the proof (blueprint: lem-trf-rational-field-tensor-local-cm).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct BigOperators

namespace Algebra.TensorProduct

/-- Tensoring a finite purely transcendental field extension with a field gives the
localization of a polynomial ring at the nonzero polynomials over the base field.
The isomorphism has the specified monomial-fraction formula. The tensor ring is
Noetherian, and every prime localization is a Noetherian local ring with depth equal
to Krull dimension.

Source: Stacks Project, Algebra, Tag 045M (lemma-tensor-fields-CM), last two sentences
of the proof (blueprint: lem-trf-rational-field-tensor-local-cm).

Proof:
1. Write B = k[x_1,...,x_r] and S = B minus zero. Injectivity of evaluation identifies
   S⁻¹B with the subfield of F consisting of fractions f(t)/s(t). This is all of F:
   it contains k and the t_i, and the field-generation hypothesis applies. Fractions
   are closed under sums and products; a nonzero f(t)/s(t) has inverse s(t)/f(t).
   Equality of two fractions follows from injectivity applied to fs' - f's.
   Coefficient inclusion into P is injective, so its image W of S excludes zero.
2. Identify B tensor L with P = L[x_1,...,x_r] by f tensor l mapping to l f.
   Its inverse sends each coefficient monomial l x^a to x^a tensor l. Check the
   composites on monomials and pure tensors, and multiplication on these generators.
3. Apply lem-weil-pbc-localization-tensor-over-base to R=k, A=M=B, T=S and N=L.
   Under steps 1 and 2 this gives W⁻¹P equivalent to F tensor L. The fraction formula
   proves multiplicativity: the product of (f tensor l)/s and (g tensor m)/u is
   (fg tensor lm)/(su), and its image is (f(t)g(t)/(s(t)u(t))) tensor lm, the
   product of the two images. Additivity handles sums of pure tensors. The unit
   maps to 1 tensor 1 and l maps to 1 tensor l, so this is an L-algebra isomorphism
   with the asserted value on every monomial fraction.
4. A field L is Noetherian, has only the prime (0), and has dimension and depth zero:
   the empty regular sequence exists, while every nonempty sequence in (0) starts
   with zero. Its localization at (0) is L. These verify the field base case of
   lem-trf-polynomial-algebra-cm.
5. That polynomial-algebra theorem gives Noetherianity and the depth-dimension
   equality at every prime of P. Apply lem-weil-pbc-localization-noetherian to W,
   then transfer Noetherianity along the isomorphism of step 3.
6. For a prime p of W⁻¹P, contract to q in P. The elements of W avoid q. Identify
   P_q with (W⁻¹P)_p by a/b mapping to (a/1)/(b/1), with inverse sending
   (a/w)/(b/v) to av/(wb). Here b/v outside p implies b outside q, and w is
   outside q, so wb is an allowed denominator. Cross multiplication verifies
   independence of representatives; substitution verifies both inverse identities.
   Prime localization is local and Noetherian by localization-noetherian. The
   isomorphism preserves prime chains and regular sequences on successive quotients,
   hence dimension and depth, giving the required equality from step 5.
-/
theorem rationalField_localization_and_local_depth_eq_dimension
    (k : Type u) (F : Type v) (L : Type w) [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] (r : ℕ) (t : Fin r → F)
    (hind : Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin r) k →ₐ[k] F))
    (hgen : IntermediateField.adjoin k (Set.range t) = ⊤) :
    ∃ e : @AlgEquiv L
        (Localization ((nonZeroDivisors (MvPolynomial (Fin r) k)).map
          (MvPolynomial.map (algebraMap k L))))
        (F ⊗[k] L) _ _ _ _ (rightAlgebra (R := k) (A := F) (B := L)),
      (∀ (α : Fin r →₀ ℕ) (l : L) (s : nonZeroDivisors (MvPolynomial (Fin r) k)),
        e (Localization.mk (MvPolynomial.monomial α l)
          ⟨MvPolynomial.map (algebraMap k L) s, ⟨s, s.property, rfl⟩⟩) =
            ((∏ i : Fin r, t i ^ α i) / MvPolynomial.aeval t (s : MvPolynomial (Fin r) k))
              ⊗ₜ[k] l) ∧
      IsNoetherianRing (F ⊗[k] L) ∧
      ∀ (p : Ideal (F ⊗[k] L)) [p.IsPrime],
        IsNoetherianRing (Localization.AtPrime p) ∧
        IsLocalRing (Localization.AtPrime p) ∧
        (IsLocalRing.depth (R := Localization.AtPrime p)
          (Localization.AtPrime p) : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p) := by
  sorry

end Algebra.TensorProduct
