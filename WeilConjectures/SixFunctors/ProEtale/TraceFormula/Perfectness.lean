/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs

/-!
# Perfectness of compactly supported cohomology

For a complex `K ∈ Dᵇctf(X, A)` on a geometric scheme `a_X : X ⟶ Spec Ω` over an algebraically
closed field, the compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K` is perfect. Perfectness
is rendered as dualizability, `HasRightDual`, as in the statement of the trace formula.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.nonempty_hasRightDual_rightDerivedLowerShriek`:
  `RΓ_c(X, K)` is dualizable.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.GeometricOperations

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Compact-support perfectness: for `K ∈ Dᵇctf(X, A)` on a geometric scheme
`a_X : X ⟶ Spec Ω`, `Ω` algebraically closed, the compactly supported cohomology
`RΓ_c(X, K) = Ra_{X!} K` is perfect, that is, dualizable in `D(Spec Ω, A)`
(blueprint: `prop-trf-compact-support-perfectness`, subsection `sk-prop-sf-trace-perfectness`). -/
theorem nonempty_hasRightDual_rightDerivedLowerShriek {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {X : Scheme.{u}} (aX : X ⟶ Spec (.of Ω))
    [IsGeometric aX] [HasCompactification aX]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K) :
    Nonempty (HasRightDual ((rightDerivedLowerShriek A aX).obj K)) :=
  sorry

end AlgebraicGeometry.ProEtale.GeometricOperations
