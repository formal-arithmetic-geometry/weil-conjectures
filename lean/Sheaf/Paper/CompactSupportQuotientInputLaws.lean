/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientCocycleData
public import Sheaf.Paper.CompactSupportQuotientNative

/-! # Identity and composition of the normalized quotient reduction arrows

Source: blueprint coefficient quotient proof, Step 4; Stacks Tag 03EK.
(blueprint: lem-coef-compact-support-quotient-input-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized quotient reductions satisfy identity and composition before applying
any geometric functor.

Source: blueprint `lem-coef-integral-compact-support.proof.md`, paragraph 2, and
Step 4 of `lem-coef-compact-support-quotient-cocycle`; Stacks Tag 03EK.
(blueprint: lem-coef-compact-support-quotient-input-laws).

Proof: the definition of rho is the unique transpose of the level-n unit under the
integral-to-level-m adjunction. On a common flat-term K-flat representative P, its
termwise formula is s tensor x to q(s) tensor x. For equal levels the quotient is the
identity. For r >= m >= n, the successive maps send s tensor x to
q_mn(q_rm(s)) tensor x = q_rn(s) tensor x. These identities hold on tensors,
descend through sheafification, and commute with differentials. Localization and the
normalized adjunct uniqueness identify these maps with the prescribed derived arrows.
The restriction identifications are exactly the sectionwise identities defining
compactSupportQuotientNativeResId and compactSupportQuotientNativeResComp. This applies to unbounded
P, the zero complex, and repeated indices, and uses no flatness of a quotient map. -/
theorem compactSupportQuotient_input_laws (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E W n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E W n).hom.app
        ((compactSupportQuotientNativeLevel l E W n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E W r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E W r m hrm).map
              (compactSupportQuotientNativeMap l E W m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E W r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E W n).obj K) =
        compactSupportQuotientNativeMap l E W r n (hmn.trans hrm) K) := by
  sorry

end WeilConjectures
