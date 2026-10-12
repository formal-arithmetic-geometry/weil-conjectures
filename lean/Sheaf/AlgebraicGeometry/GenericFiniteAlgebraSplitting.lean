module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Spec
import Sheaf.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Sheaf.AlgebraicGeometry.SpreadPurelyInseparableFactors
import Sheaf.FieldTheory.GenericSeparableAlgebraSplitting

/-!
# Generic splitting of a finite algebra after an étale base change

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9
(blueprint: lem-weil-pbc-generic-finite-algebra-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open AlgebraicGeometry

/--
A finite algebra `B` over a Noetherian domain `A` splits generically: after inverting a nonzero
`c` and a finite étale surjective base change `A[1/c] → A'`, the reduction of `B ⊗[A] A'` is a
finite product of finite `A'`-domains `D j`, each `Spec (D j) → Spec A'` finite, surjective and a
universal homeomorphism (every base change a homeomorphism). The fraction field `K` of the node
is only named there; it is not a datum of the statement.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof steps 4--9
(blueprint: lem-weil-pbc-generic-finite-algebra-splitting).

Proof: pass to the generic fibre `C = B ⊗[A] K`, a finite-dimensional `K`-algebra, and apply
`lem-weil-pbc-generic-separable-algebra-splitting`: after a finite separable `K'/K` the
reduction of `C ⊗[K] K'` is a product of finite purely inseparable fields `L j`. Spread `K'/K`
to a finite étale surjective `A[1/c] → A'` by `lem-weil-pbc-spread-finite-separable-extension`.
After a further principal localization, `(B ⊗[A] A')_red` is torsion free with generic fibre
`(C ⊗[K] K')_red = ∏ L j` (reduction commutes with localization); clearing denominators in the
generic idempotents splits it as a product of finite domains `D j` with fraction fields `L j`.
Each `A' → D j` is then finite, surjective and a universal homeomorphism by
`lem-weil-pbc-spread-purely-inseparable-factors`.
-/
theorem exists_generic_finite_algebra_splitting
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B] :
    ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
      (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A'),
      c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
        Algebra.Etale (Localization.Away c) A' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))) ∧
        ∃ (r : ℕ) (D : Fin r → Type u) (_ : ∀ j, CommRing (D j))
          (_ : ∀ j, Algebra A' (D j)),
          (∀ j, Module.Finite A' (D j) ∧ IsDomain (D j) ∧
            IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))) ∧
            Surjective (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))) ∧
            (topologically IsHomeomorph).universally
              (Spec.map (CommRingCat.ofHom (algebraMap A' (D j))))) ∧
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
          Nonempty (((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) ≃ₐ[A'] (∀ j, D j)) := by
  sorry
