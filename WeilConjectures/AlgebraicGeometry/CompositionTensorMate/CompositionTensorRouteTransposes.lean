/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData

/-! # The two successive tensor transposes

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence.proof.md, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CompositionTensorMate

/-- The formal composition calculation on the actual finite-Tor domains.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence.proof.md, Step 2
(blueprint: lem-pur-composition-tensor-route-transposes).

Proof: first restrict the standing Hom bijections to the full etale-origin classes.
The actual compact-support compositor is a natural isomorphism on these classes.
Transport the composite adjunction by this isomorphism and apply right-adjoint
uniqueness. Its component is the explicit c: successive application of the two Hom
bijections to alpha followed by the composite-map counit. The uniqueness counit
identity proves the displayed mate equation; its naturality and invertibility give
MateClause on bounded constructibles, which belong to the origin classes.
Then transpose through the standing f and g Hom bijections. Their naturality moves
S_f(theta_g) across the first transpose. Substituting the defining theta transposes
leaves inverse f-projection, f-counit, inverse g-projection, g-counit, in that order.
Coefficient associativity for the inverse f-projection and naturality for the inverse
g-projection identify this with compositePi followed by t tensor identity and the
left unitor. For the other route, the defining mate equation for c replaces its
composite transpose by alpha followed by the h-counit. Naturality of alpha and the
compact-support projection-composition identity give the same compositePi. Move
c at the unit through the source-factor projection and cancel it with its inverse
in sigma; the remaining trace is t. Injectivity of the composite Hom bijection
proves equality. The same computations at the coefficient unit give UnitTransposeClause.
All equalities commute with coefficient morphisms because the projection, counit,
pullback compositor, tensor constraints and the Hom bijections are natural.
All inverses occur on the explicitly supplied domains; zero inputs and empty schemes
use the same equations and introduce no extra hypotheses. -/
theorem compositionTensorRouteTransposes
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [UpperStarPreservesFlat (ModuleCat.{u + 1} A)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (huY : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y (unit A Y))
    (huZ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z (unit A Z))
    (hf : TensorClause A f) (hg : TensorClause A g) (hh : TensorClause A (f ≫ g))
    (hdom : ∀ K : D A Z, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) Z K →
      genericDomains (ModuleCat.{u + 1} A) f g (omega A f) (W A f g) (omega A g)
        (G A g) (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X)
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y) K) :
    MateClause A f g ∧ UnitTransposeClause A f g ∧
    ∀ K : D A Z, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z K →
      routeEquations (F A f ⋙ F A g)
        (genericSource (ModuleCat.{u + 1} A) Z (f ≫ g) (W A f g)) (G A g ⋙ G A f)
        (lhs A f g) (rhs A f g) (compositeEpsilon A f g) (commonTranspose A f g)
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z) K := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionTensorMate
