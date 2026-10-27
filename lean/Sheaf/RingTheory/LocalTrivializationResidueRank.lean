module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.Torsion.Basic

import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Local trivializations and maximal residue rank

Source: Stacks Project, Algebra, Tag 02M9, first proof hint, with the fraction
comparisons of Tags 07JZ and 00DK made explicit
(blueprint: lem-a1-local-trivialization-residue-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- A principal rank-`r` trivialization near a maximal ideal gives rank `r` at that
maximal localization and in the residue module, with the canonical residue comparisons.

Source: Stacks Project, Algebra, Tag 02M9, first proof hint; Tags 07JZ and 00DK
(blueprint: lem-a1-local-trivialization-residue-rank).

The submodule `q • ⊤` of the localized module is formed after restriction to `E`;
it is exactly the submodule of finite sums of `q`-multiples, hence is also the
submodule usually written `q P_q`. Its quotient carries the canonical `E/q` action
from `Module.IsTorsionBySet.module`. The ring comparison is specified on every
representative, and so is the module comparison. A basis on `Fin r` expresses
freeness of rank `r`, including rank zero. `Module.Finite` makes finite dimensionality
explicit rather than relying on the infinite-dimensional convention for `finrank`.

Proof:
1. Since `q` is maximal, `E/q` is a field
   (`lem-weil-common-extension-fields-quotient-field`). For `s ∉ q`, its residue
   is invertible. Fractions give the ring map `E_f → E_q`, `a/f^n ↦ a/f^n`,
   and the surjection `E_q → E/q`, `a/s ↦ ā/s̄`, with kernel `q E_q`.
   Thus the canonical map `E/q → E_q/q E_q` is a ring isomorphism.
2. Using `def-weil-pbc-module-tensor-product`, define inverse `E_q`-linear maps
   `E_q ⊗[E_f] P_f → P_q` and `P_q → E_q ⊗[E_f] P_f` by
   `(a/s) ⊗ (p/f^n) ↦ ap/(s f^n)` and `p/s ↦ (1/s) ⊗ (p/1)`.
   Fraction equalities give well-defined maps: cancel the witnessing power of `f`
   or element of `E ∖ q`, which becomes invertible. Balancing holds by multiplying
   denominators. On pure tensors and fractions the composites are identities.
3. The assumed basis of `P_f` base changes to a basis of the tensor product by
   `lem-weil-pbc-free-module-base-change-free` (`Module.Basis.baseChange`).
   Transport through the preceding comparison to obtain the asserted basis of `P_q`.
4. The map `p ↦ [p/1]` kills `q P`, so descends to the residue quotients.
   Its inverse is `[p/s] ↦ s̄⁻¹[p]`: reduction of a witnessed fraction equality
   and division by the nonzero residues proves well-definedness and linearity.
   It kills `q P_q`. The first composite fixes `[p]`. For the other, lift `s̄⁻¹`
   to `t ∈ E`; since `ts - 1 ∈ q`, `[tp/1] = [p/s]`. These arguments apply to
   arbitrary modules without a finite-generation assumption.
5. Coordinates in the basis of `P_q` carry `q P_q` onto `(q E_q)^r`:
   one inclusion follows by taking coordinates of finite sums of `q`-multiples,
   and the reverse by expanding each of the finitely many coordinates into such sums.
   Reducing coordinates gives `P_q/q P_q ≃ (E/q)^r`. Compose with the residue
   comparison to get a basis of `P/q P` on `Fin r`. Thus it is finite dimensional
   and its `Module.finrank` is `r` (`def-weil-vector-space-dimension`). Empty
   coordinates cover `r = 0`; the zero ring has no maximal ideal. -/
theorem local_trivialization_residue_rank
    {E : Type u} [CommRing E] (P : Type v) [AddCommGroup P] [Module E P]
    (q : Ideal E) [q.IsMaximal] (f : E) (hf : f ∉ q) (r : ℕ)
    (hfree : Nonempty (Module.Basis (Fin r) (Localization.Away f)
      (LocalizedModule.Away f P))) :
    Nonempty (Module.Basis (Fin r) (Localization.AtPrime q)
      (LocalizedModule q.primeCompl P)) ∧
    (∃ e : (E ⧸ q) ≃+*
        (Localization.AtPrime q ⧸ Ideal.map (algebraMap E (Localization.AtPrime q)) q),
      ∀ a : E, e (Ideal.Quotient.mk q a) =
        Ideal.Quotient.mk (Ideal.map (algebraMap E (Localization.AtPrime q)) q)
          (algebraMap E (Localization.AtPrime q) a)) ∧
    (∃ e : (P ⧸ q • (⊤ : Submodule E P)) ≃ₗ[E ⧸ q]
        ((LocalizedModule q.primeCompl P) ⧸
          q • (⊤ : Submodule E (LocalizedModule q.primeCompl P))),
      ∀ p : P, e (Submodule.Quotient.mk p) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap q.primeCompl P p)) ∧
    Module.Finite (E ⧸ q) (P ⧸ q • (⊤ : Submodule E P)) ∧
    Module.finrank (E ⧸ q) (P ⧸ q • (⊤ : Submodule E P)) = r := by
  sorry

end Module
