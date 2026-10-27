module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.RingTheory.PowerSeriesRingSubfields
import WeilConjectures.RingTheory.PBasisComplementMonomialBasis
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis

/-!
# Stabilized generic rank of completed differentials

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, 2.1.5–2.1.6,
printed pp.50–51, equations (2.a) and (2.b), and Proposition 1.2.4.
(blueprint: lem-per-cofinite-pbasis-completed-generic-rank)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open TensorProduct

namespace RingTheory

/-- Deleting a sufficiently large finite part of a coefficient p-basis gives completed
relative differentials of generic rank `d + J.card`.

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, 2.1.5–2.1.6,
printed pp.50–51, equations (2.a) and (2.b), and Proposition 1.2.4.
(blueprint: lem-per-cofinite-pbasis-completed-generic-rank)

The algebra maps from `F J` are the composites of its subfield inclusion with the
fixed coefficient-field embedding, as specified by `hcomp`. The completion is the
inverse limit of the quotients of the differential module by maximal-ideal powers.

Proof:
1. Use `lem-weil-pbc-noetherian-local-system-of-parameters` to choose d parameters.
   Case (a) of `lem-per-parameter-ideal-formal-normalization` gives a finite injective
   parameter map R = k[[t_1,...,t_d]] into A, hence a finite extension L/K of fraction
   fields. A domain is reduced and equidimensional, so all hypotheses hold for the
   fixed coefficient field.
2. Put R_J = F_J[[t_1^p,...,t_d^p]] and K_J = Frac(R_J). Apply
   `lem-weil-pbc-power-series-ring-subfields` with n = d and m = 0. It gives finiteness
   over R_J, containment of K^p, intersection K^p and the decreasing-family condition.
   Localizing the finite ring extension gives a finite-dimensional domain over K_J,
   hence a field equal to K. The index family contains the empty finite set.
3. By `lem-weil-pbc-p-basis-complement-monomial-basis`, bounded coefficient monomials
   on J form an F_J-basis of k. Expanding coefficients and grouping parameter exponents
   modulo p gives an R_J-basis of R on the bounded coefficient and parameter monomials.
   Clearing denominators proves independence over K_J; f/g = f*g^(p-1)/g^p proves
   spanning. This is a relative p-basis of K/K_J. Apply
   `lem-weil-pbc-p-basis-differentials-basis` to get differential dimension d + |J|.
4. Apply `lem-per-cofinite-subfields-finite-extension-differential-rank` to L/K and
   (K_J). It gives J0 such that every J containing J0 has
   dim_L Omega(L/K_J) = dim_K Omega(K/K_J) = d + |J|.
5. The coefficient basis makes R finite free over F_J[[t_1,...,t_d]], so A is finite
   over that ring. Its evaluation into A is local and continuous. Apply
   `lem-per-pth-power-series-completed-differential-comparison`: its p-power subring
   is R_J and it identifies the completed differential module with Omega(A/R_J).
6. Apply `lem-weil-pbc-kahler-differentials-localization` to pass to L. A derivation
   on L vanishing on R_J also kills inverses, by D(1/s) = -D(s)/s^2, and therefore
   kills K_J. The universal property in `def-weil-pbc-kahler-differentials` identifies
   Omega(L/R_J) with Omega(L/K_J). Taking dimensions and using step 4 proves the
   claimed rank for every finite J containing J0. Tensor symmetry gives the displayed
   scalar-extension order. -/
theorem cofinitePBasisCompletedGenericRank
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    (d : ℕ) (hd : 1 ≤ d) (hdim : ringKrullDim A = d)
    (k : Type v) [Field k] [Algebra k A] [CharP k p]
    (hres : Function.Bijective ((IsLocalRing.residue A).comp (algebraMap k A)))
    (E : Type w) (β : E → k)
    (hpb : ∃ b : Module.Basis {a : E →₀ ℕ // ∀ i : E, a i < p}
      (Subfield.closure (Set.range (fun x : k ↦ x ^ p))) k,
      ∀ a, b a = (a : E →₀ ℕ).prod (fun i e ↦ β i ^ e))
    (F : Finset E → Subfield k)
    (hF : ∀ J : Finset E, F J = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : E, i ∉ J ∧ β i = x}))
    [∀ J : Finset E, Algebra (F J) A]
    (hcomp : ∀ (J : Finset E) (x : F J), algebraMap (F J) A x = algebraMap k A (x : k))
    (L : Type z) [Field L] [Algebra A L] [IsFractionRing A L] :
    ∃ J0 : Finset E, ∀ J : Finset E, J0 ⊆ J →
      Module.rank L (L ⊗[A]
        AdicCompletion (IsLocalRing.maximalIdeal A) (KaehlerDifferential (F J) A)) =
          (d + J.card : ℕ) := by
  sorry

end RingTheory
