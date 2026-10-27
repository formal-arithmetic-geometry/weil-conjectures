/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.IntegralGeometricComparisonData

/-! # A component of integral geometric comparison realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X' X Y' Y : Scheme.{u}} {gx : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {gy : Y' ⟶ Y} {sq : IsPullback gx f' f gy}
  {c : Compactification f}
  [∀ z : X, Invertible (l : X.residueField z)]
  [∀ z : Y, Invertible (l : Y.residueField z)]
  [∀ z : X', Invertible (l : X'.residueField z)]
  [∀ z : Y', Invertible (l : Y'.residueField z)]
  (a : SpTowerMate.Data l E b o q sq c)
  (s : SpExceptionalBaseChange.IntegralData l E b o q a)
  [QuasiCompact f] [QuasiCompact f']
  [QuasiCompact (c.i ≫ c.g)] [HasCompactification (c.i ≫ c.g)]
  [QuasiCompact ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]
  [HasCompactification ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]

/-- The completed support comparison is exactly the reconstruction of the strict mate.
Source: latest blueprint integral geometric realization, Step 8; compact support transport.
(blueprint: lem-pur-integral-geometric-support-realization).

Proof: identify the small-site completed coefficients with the completed constant
coefficient model by their quotient projections. The scalar-derived comparison transports
the proper direct-image mate and the open inverse mate; their composite supplies support,
with the stated scalar-restriction normalization. On the pulled-back compactification take
gbar to be the actual pullback projection. The chosen Cartesian square and open square
are its universal-property maps. Constructibility gives derived completeness for every
finite generating tuple of the same adic ideal. Strict integral exchange normalization
identifies the proper factor before total limit, while its unit equation fixes the open
factor. Semilinear exchange reindexing identifies the ordered composite. Reconstruct it
through the normalized equivalence: full faithfulness gives beta and its reduction
equation, while the same before-localization factorization gives CompletedExchange.equation.
The quotient, tensor-unit and augmentation equations give CoefficientTransport, including
its pull_normalization. No equality is inferred just from finite evaluations. An empty
generating tuple is handled by the same derived-completeness property and Koszul definition.
-/
theorem integral_geometric_support_realization [IsIso gx] [IsIso gy]
    (x : SpTowerShriek.OpenExchange l E b o)
    (_hb : IsIso (SpTowerMate.beta l E b o q a x)) :
    ∃ t : CoefficientTransport l E,
    ∃ beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E gy ≅
      constructibleIntegralPullback l E gx ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed',
      Nonempty (CompletedExchange l E b o q a s t beta) ∧
      ∀ K : sfIntegralConstructibleCategory l E X,
        (SpExceptionalBaseChange.red l E b q s.rY').map (beta.hom.app K) =
          SpExceptionalBaseChange.exchangeReduction l E b o q a s x K := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
