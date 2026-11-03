/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralCurrentLimitFactorization

/-! # Native factor of the compact-support/limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified proper/total-limit mate is invertible on whole derived towers.

Source: latest blueprint, integral direct-image proof (2), proper factor and
whole-diagram scalar restriction; Stacks Tags 0A07 and 0D6E.
(blueprint: lem-sp-current-proper-limit-mate).

Proof in words:
1. On the diagram sites, restrict the finite quotient actions to the pulled-back
integral ring. The two factorizations of the same ringed-topos morphism give the
proper scalar-restriction comparison, normalized by their composite derived units.
This is an isomorphism before evaluating a level.
2. Right adjoints preserve inverse limits. Derive the composite on a simultaneous
K-injective diagram resolution; the proper direct-image/strict-limit theorem
identifies the two total right derived composites and their comparison maps.
3. The coefficient isomorphisms agree sectionwise with the prescribed projections.
Transport through the section-module and tower realization equivalences. Uniqueness
of the total right derived functors identifies these with the given A, including its
ordinary-unit and K-injective normalizations.
4. Transpose the scalar/pullback square first through the geometric adjunctions and
then through reduction/limit. The iterated-mates identity identifies the result with
the conjugate comparison of the composite adjunctions. It is exactly properLimitMate,
since nativeProperScalar is the first transpose in the same realization coordinates.
The conjugate of the inverse pinned pullback isomorphism is invertible. Thus every
component is invertible, on the whole unbounded derived tower category. The proof
also applies to the empty scheme and zero diagram. -/
theorem proper_limit_mate_isIso (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (C : spDerivedCoefficientTowers l E X (s.towers X)) :
    IsIso ((properLimitMate l E s q A f).app C) := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
