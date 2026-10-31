/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationOrdinaryScalarAssembly

/-! # Horizontal scalar compatibility and direct-image acyclicity
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-transition-acyclicity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed finite scalar components respect all horizontal arrows, and fixed
ring direct image is computed by forgotten K-injective coefficient-system complexes.
This involves no choice of reduction or total-limit presentation.
Source: blueprint direct-image proof, paragraph (2), comparisons on strict systems;
Stacks Project, Tags 03DI, 03D7 and 0D6E.
(blueprint: lem-sp-compactification-scalar-transition-acyclicity).

Proof: transpose the open horizontal square through the recorded ordinary open
adjunctions. The normalized finite unit equations and ordinaryUnitTransition identify
the two transposes: each scalar restriction preserves the open unit, and on extension
summands the scalar map leaves the underlying section unchanged. The same calculation
is retained by both identity-on-sections evaluation transports. Adjunction injectivity
then gives coherence of openLevelScalar for every horizontal arrow. For pushforward,
realize the coefficient systems on the ringed diagram sites with completed constant
ring diagram and finite quotient diagram. The maps between these diagrams are the
completed quotient projections. Their compatibility with inverse image is h. Apply
diagramRingRestrictionPushforward. Transport its ordinary comparison through the
recorded exact section presentations; its identity-on-sections normalization agrees
with pushLevelScalar, since ordinaryPushScalar is the same restriction/direct-image
comparison and the evaluation comparisons preserve sections. Its naturality in the
index is thus coherence of pushLevelScalar. Finally compose the identity-site
coefficient restriction ringed-topos morphism with fixed-ring geometric direct image.
The ringed-topos derived composition theorem identifies this composite with finite
coefficient direct image followed by exact restriction. At a K-injective coefficient
system complex the restriction-derived unit and the composite-derived unit are
invertible. Their composition-unit equation and the invertible composition comparison
force the fixed-ring derived unit on the restricted complex to be invertible. Exact
section-equivalence transport gives the stated canonical rightDerivedFunctorUnitQ.
This proves acyclicity, without claiming restriction preserves K-injectives. The
argument includes identity arrows and all unbounded complexes. -/
theorem compactificationScalarTransitionAcyclicity
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (h : ScalarSquares l E) (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace c.Z] [QuasiSeparatedSpace c.Z]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (_hX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hZ : ∀ x : c.Z, IsUnit (l : c.Z.residueField x))
    (_hY : ∀ x : Y, IsUnit (l : Y.residueField x)) [QuasiCompact c.i]
    (DX : SpCoefficientTowersAbelian l E X)
    (DZ : SpCoefficientTowersAbelian l E c.Z) (DY : SpCoefficientTowersAbelian l E Y)
    (vX : Evaluation l E b X DX) (vZ : Evaluation l E b c.Z DZ)
    (vY : Evaluation l E b Y DY) :
    ScalarLevelCoherent (forgetting l E X DX ⋙ fixedOpenOrd l E c.i)
        (ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ)
        (openLevelScalar l E b o h c.i DX DZ vX vZ) ∧
      ScalarLevelCoherent (forgetting l E c.Z DZ ⋙ fixedPushOrd l E c.g)
        (ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y DY)
        (pushLevelScalar l E b o h c.g DZ DY vZ vY) ∧
      (∀ I : CochainComplex (spCoefficientTowers l E c.Z) ℤ, I.IsKInjective →
        IsIso ((fixedPushOrd l E c.g).rightDerivedFunctorUnitQ
          (((forgetting l E c.Z DZ).mapHomologicalComplex (.up ℤ)).obj I))) := by sorry

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
