/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Optional ambient exceptional-adjoint admissibility

Source: latest blueprint, sec-six-functors-basics/sk-prop-sf-existence,
`def-weil-exceptional-adjoint-admissibility.md`, clauses (1)--(3) and condensed paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility).

These are hypotheses about ambient right adjoints, distinct from the constructible
exceptional inverse image. No admissibility of smooth proper morphisms is asserted.
The finite definition uses exactly the chosen compactification and the recorded FullCD.
The condensed definition is at the coefficient ring itself, with refinement coherence;
there are no conditions on finite reductions or changes of coefficient rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The same finite-stage definition for any finite commutative coefficient ring.
The intrinsic constructibility predicate is reused through the canonical equivalence
between constant-ring modules and sheaves valued in modules. The conjunction with
ordinary finite Tor amplitude defines exactly the finite-Tor domain.
Source: latest blueprint `def-weil-exceptional-adjoint-admissibility`, opening generality
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
def IsExceptionalAdjointAdmissibleAtFiniteRing
    (A : Type u) [CommRing A] [Finite A]
    {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y}
    (c : AlgebraicGeometry.Compactification f) : Prop :=
  (∃ cCD : ℕ, AlgebraicGeometry.Scheme.sfFullCohomologicalDimension c.g A cCD) ∧
  (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A c).IsLeftAdjoint ∧
  (∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y A ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X A),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A c ⊣ G) →
    (AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
      (ULift.{u + 1, u} A) Y).inverseImage
        (AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Y A).inverse ≤
      ((AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
        (ULift.{u + 1, u} A) X).inverseImage
          (AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence X A).inverse).inverseImage G) ∧
  (∃ cMinus cPlus : ℤ, ∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y A ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X A),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A c ⊣ G) →
    ∀ a b : ℤ, a ≤ b → ∀ L,
      AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
        (ULift.{u + 1, u} A) Y
        ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Y A).inverse.obj L) →
      DerivedCategory.homologyConcentratedIn a b L →
      AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
        (ULift.{u + 1, u} A) X
        ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence X A).inverse.obj (G.obj L)) ∧
      DerivedCategory.homologyConcentratedIn (a + cMinus) (b + cPlus) (G.obj L)) ∧
  ∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y A ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X A),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A c ⊣ G) → ∀ L,
      AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
        (ULift.{u + 1, u} A) Y
        ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Y A).inverse.obj L) →
      AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude Y A L →
      AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic
        (ULift.{u + 1, u} A) X
        ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence X A).inverse.obj (G.obj L)) ∧
      AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude X A (G.obj L)

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
