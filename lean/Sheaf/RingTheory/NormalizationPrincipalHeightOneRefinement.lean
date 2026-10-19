module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.TraceFormula.NormalizationFiniteLocalModel

/-!
# Principal height-one refinement in a normalization

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Theorem 4.10.5, printed p. 91 (PDF p. 105), principal-height subclaim
(blueprint: lem-trf-normalization-principal-height-one-refinement).

## Main statement

* `normalization_principal_height_one_refinement`: in the integral closure of a
  Noetherian local domain in its fraction field, every prime containing a
  nonzero element contains a height-one prime containing that element.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

@[expose] public section

namespace RingTheory

/-- Every prime containing a nonzero element of a local Noetherian domain's
normalization contains a height-one prime containing that element.

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Theorem 4.10.5, printed p. 91 (PDF p. 105), principal-height subclaim
(blueprint: lem-trf-normalization-principal-height-one-refinement).

Proof: For `0 ≠ b` in the normalization `N` and a prime `P` containing `b`,
put `S = R[b]`.  This is a finite-type Noetherian domain, integral over `R`,
and its integral closure in `Frac R` is again `N`.  Apply the finite-local-model
lemma to `S`, obtaining a Noetherian local domain `A` whose normalization is
`N_P`.  A minimal prime over `bA` below `P ∩ A` has height at most one by the
Noetherian principal height bound, and has height exactly one because `b` is
nonzero.  Lying over gives a prime in `N_P` over it; incomparability bounds its
height by one.  Contracting through the localization prime correspondence
produces a nonzero prime `Q ⊆ P` containing `b` with height one.
-/
theorem normalization_principal_height_one_refinement
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (b : integralClosure R (FractionRing R)) (hb : b ≠ 0)
    (P : Ideal (integralClosure R (FractionRing R))) [P.IsPrime]
    (hbP : b ∈ P) :
    ∃ Q : Ideal (integralClosure R (FractionRing R)),
      Q.IsPrime ∧
        Q ≠ ⊥ ∧
          (∀ Q' : Ideal (integralClosure R (FractionRing R)),
            Q'.IsPrime → Q' < Q → Q' = ⊥) ∧
            Q ≤ P ∧ b ∈ Q := by
  sorry

end RingTheory

end
