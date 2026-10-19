/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint
import Sheaf.AlgebraicGeometry.CompactSupportProjectionOpenRestriction
import Sheaf.AlgebraicGeometry.TraitDualizingScalarRestriction

/-!
# Proper invertible-degree descent of punctual cohomological purity

Source: ILO, Exposé XVI, Proposition 3.5.7 and Lemmas 3.5.8--3.5.10, pp.249--250;
Definition 3.2.1 (blueprint: lem-per-punctual-purity-proper-degree-descent).

The purity hypothesis and conclusion use the published punctual-purity predicate,
whose local class is the canonical transpose of the supported Kummer class.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper dominant generically etale maps of degree prime to ell descend punctual purity
between integral regular finite-type quasi-projective schemes over the specified trait.

Source: ILO XVI Proposition 3.5.7 and Lemmas 3.5.8--3.5.10, pp.249--250
(blueprint: lem-per-punctual-purity-proper-degree-descent).

Proof:
1. By lem-per-prepurity-lci-classes, the normalized relative classes satisfy
   c_V = f^!(c_W) g, with equal virtual dimensions and f^!K_W = K_V.
   lem-per-trait-relative-class-criterion makes c_V invertible by punctual purity of V.
2. Transpose g to t : Rf_* A_V -> A_W. The proper projection formula
   lem-amb-proper-coproducts-projection defines T_M and its transpose a_M, naturally in M.
   Use def-amb-etale-compact-support and thm-amb-etale-exceptional-adjoint.
3. Put H = Rf_* c_V, i_A = u_A, r_A = t, i_K = Rf_* a_K u_K, r_K = epsilon_K.
   Naturality and the composition identity give H i_A = i_K c_W and r_K H = c_W r_A.
4. Restrict to the nonempty finite-etale open of degree d. The open-exchange and
   projection-restriction lemmas lem-amb-shriek-open-exchange-adjoint and
   lem-amb-shriek-projection-open-restriction identify these maps with their restrictions.
   lem-per-finite-etale-derived-ambidexterity makes both composites d times identity.
5. End(A_W) = A because W is integral and connected; restriction to that open is injective.
   For K_W use lem-per-trait-dualizing-scalar-restriction, without assuming purity of W.
   Hence r_A i_A = d and r_K i_K = d globally.
6. In F_ell the scalar d has inverse b. The explicit inverse of c_W is
   b r_A H^(-1) i_K. The two equations of step 3 and scalar identities of step 5
   verify both inverse equations. No flatness of f is used.
7. lem-per-trait-relative-class-criterion converts invertibility of c_W to the local
   Kummer-class isomorphism at every point, exactly the predicate IsPunctuallyPure.
-/
theorem punctual_purity_of_proper_primeToDegree
    (ℓ : ℕ) (hℓ : ℓ.Prime) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CharZero (FractionRing R)]
    (hres : 0 < ringChar (IsLocalRing.ResidueField R)) (hℓR : IsUnit (ℓ : R))
    {V W : Scheme.{u}} [V.Over (Spec (.of R))] [W.Over (Spec (.of R))]
    [IsIntegral V] [IsIntegral W] (hV : IsRegularScheme V) (hW : IsRegularScheme W)
    [LocallyOfFiniteType (V ↘ Spec (.of R))] [QuasiCompact (V ↘ Spec (.of R))]
    [LocallyOfFiniteType (W ↘ Spec (.of R))] [QuasiCompact (W ↘ Spec (.of R))]
    (hVqp : ∃ (N : Type u) (_ : Finite N) (i : V ⟶ ℙ(N; Spec (.of R))),
      IsImmersion i ∧ i ≫ (ℙ(N; Spec (.of R)) ↘ Spec (.of R)) = V ↘ Spec (.of R))
    (hWqp : ∃ (N : Type u) (_ : Finite N) (i : W ⟶ ℙ(N; Spec (.of R))),
      IsImmersion i ∧ i ≫ (ℙ(N; Spec (.of R)) ↘ Spec (.of R)) = W ↘ Spec (.of R))
    (f : V ⟶ W) [f.IsOver (Spec (.of R))] [IsProper f] [IsDominant f]
    (d : ℕ) (hd : 0 < d) (hprime : ¬ ℓ ∣ d)
    (hgeneric : ∃ U : W.Opens, Nonempty U ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) ∧
      (f ∣_ U).IsFiniteLocallyFreeOfDegree d)
    (hpure : IsPunctuallyPure ℓ hℓ V) :
    IsPunctuallyPure ℓ hℓ W := by
  sorry

end AlgebraicGeometry.Etale
