/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations

/-! Mixed coefficient compatibility for the specified proper/open exchange. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The proper/open compact-support comparison commutes with scalar base change.
Source: blueprint mixed-base-change direct-image proof, Steps 1--5; Stacks Tags
0E47, 03S6 and 09AE (blueprint: lem-sp-mixed-compact-support-scalar).

Proof: use the coefficient-independent pullback compactification, and write its
proper Cartesian square as psq. Expand reductionDirectImageComparison as the
proper scalar mate chi followed by the proper pushforward of the open tensor map e.
Expand mixedCompactSupportExchange as proper exchange q followed by the proper
pushforward of the transported ordinary open exchange a. Naturality of q_B moves
e across q_B. For the open factor, the unit-preserving ordinary/intrinsic
realization equivalences identify the transported ordinary open exchange with the
open-adjunction mate. Indeed both transposes are the pulled-back open unit followed
by the normalized inverse-image compositor, so injectivity of the open-adjunction
Hom equivalence identifies them. The published openScalarExchange, conjugated by
reductionOpenModel, now gives the open scalar square for a and e with the specified
directImageScalarPullbackIso. Push this identity through the proper pushforward.
Apply directImageScalarExchange to the proper Cartesian square at j_A!M. Finally
naturality of the proper scalar mate at a_A moves a_A across chi'. These four
identities paste, by associativity, to the forward equation. Precompose with the
inverse target scalar/pullback comparison and postcompose with the inverse source
comparison; their inverse identities give the displayed equation. This argument is
natural on the whole ambient category, needs no constructibility, and also covers
zero modules, zero coefficient rings and empty open immersions. -/
theorem mixedCompactSupportScalar
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (M : proEtaleDerivedCategory X A) :
    (directImageScalarPullbackIso φ g).inv.app
        ((reductionCompactSupport A cpt.i cpt.g).obj M) ≫
      (proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ cpt.i cpt.g).app M) ≫
      (mixedCompactSupportExchange B sq cpt).app
        ((scalarExtensionFunctor φ X).obj M) =
    (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq cpt).app M) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
        (mixedPullbackCompactification sq cpt).g).app
          ((proEtaleConstantRingDerivedPullback A g').obj M) ≫
      (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
        (mixedPullbackCompactification sq cpt).g).map
          ((directImageScalarPullbackIso φ g').inv.app M) := by sorry

end AlgebraicGeometry.ProEtale
