/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldFiniteDualizingTowerData

/-! # Normalized lifts of finite dualizing scalar comparisons

Source: current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`.
(blueprint: lem-sf-general-field-normalized-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteDualizingTowers
namespace WeilConjectures.GeneralFieldFiniteDualizingTowers
variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed finite scalar-counit mates have a unique invertible lift between
any two specified general-field dualizing tower realizations.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, paragraph 4
(blueprint: lem-sf-general-field-normalized-tower-comparison).
Proof: transpose under the specified scalar adjunction. Its target is exact scalar
restriction of Q. Evaluation followed by the canonical restriction/evaluation square
identifies a required vertex map with P.level followed by the finite counit mate and
the inverse of the restricted Q.level. The finite coefficient comparison's reduction
square gives compatibility with adjacent transitions. Exact restriction and the common
finite dualizing lower bound bound both derived systems below. For an adjacent edge,
scalar adjunction and the finite dualizing isomorphism identify its negative Hom group
with Hom(omega,omega[-1]); foundational finite biduality and standard t-structure
orthogonality make this zero. Sequential unique lifting now constructs and uniquely
determines the adjoint map. Transpose back. The level scalar-extension/evaluation mate
is an isomorphism: ordinary evaluation commutes with the finite-free tensor functor,
and both are exact, so localization identifies their derived functors. Under this
identification every evaluation of the lift is the specified invertible finite
comparison. Joint conservativity of evaluations proves invertibility of the lift.
No coherence assertion for identities or composition is part of this lemma. -/
theorem normalized_comparison_exists
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p)
    {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
    (P : Realization k X s) (Q : Realization k X t) :
    ∃ f : A.model.T.obj P.obj ⟶ Q.obj,
      IsComparison k X a A P Q f ∧ IsIso f ∧
        ∀ g : A.model.T.obj P.obj ⟶ Q.obj,
          IsComparison k X a A P Q g → g = f := by
  sorry

end WeilConjectures.GeneralFieldFiniteDualizingTowers
