/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteCounitRestrictionData

/-! # Regular coefficient targets for finite point sections -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteCounitRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [hsep : IsSeparated (X ↘ Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

/-- The scalar-unit transitions take regular constant sections to the actual
integral-linear coefficient quotient.
Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2,
final sentences, expanded in step 4 of lem-coef-finite-counit-restriction-square
(blueprint: lem-coef-finite-counit-constant-targets).

Proof: compute the scalar adjunction unit on the regular module: a maps to a tensor 1.
The normalized scalar-unit comparison sends a tensor b to q(a)b. Thus its transpose
is the quotient a maps to q(a). The regular module, placed in degree zero, is flat
and K-flat, so these ordinary formulas compute the derived transpose as well.
The unit normalization of the comparison-site functor identifies its regular
coefficient object with the regular pro-etale sheaf. Naturality of the specified
comparison-restriction square retains the quotient formula on its constant sections.
Commuting constant sheafification with restriction of scalars, followed by the
constant-sheaf adjunction unit, sends the same element a to its constant section.
The integral restriction compositor retains that map and its integral action,
since q composed with the integral quotient is the next integral quotient. Apply
exact point sections and the single-complex functor. Naturality of their specified
single-complex comparisons gives the displayed equation with quotientMap. Both
sides send each a to the constant section of q(a); equality before localization
therefore gives the equality in D(R). This works for equal and nonflat quotient
levels, and involves no exceptional object or arbitrary derived representative. -/
theorem constant_targets :
    (∀ {m n : ℕ} (h : n ≤ m),
      targetConstantMap l E D m ≫ sectionUnitTransition l E D h =
        (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).map
          (quotientMap l E h) ≫ targetConstantMap l E D n) := by
  sorry

end WeilConjectures.FiniteCounitRestriction
