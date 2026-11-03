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

/-- Clauses (1)--(3) at the positive quotient coefficient stage. FullCD is imposed
on the chosen proper part only. The two signed constants work for every right adjoint
and every ordered input interval; no ordering of the output endpoints is required.
Right adjoints are unique up to unique adjunction-compatible isomorphism, and the
preservation predicates are invariant under isomorphism, so checking one suffices.
Source: latest blueprint `def-weil-exceptional-adjoint-admissibility`, finite clauses
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
def IsExceptionalAdjointAdmissibleAtQuotient
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y}
    (c : AlgebraicGeometry.Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (∃ cCD : ℕ, AlgebraicGeometry.Scheme.sfFullCohomologicalDimension c.g
    (Padic.coefficientExtensionRing l E n) cCD) ∧
  (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
    (Padic.coefficientExtensionRing l E n) c).IsLeftAdjoint ∧
  (∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l E n) ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X
        (Padic.coefficientExtensionRing l E n)),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E n) c ⊣ G) →
    ∀ L, AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l E n hn Y L →
      AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l E n hn X (G.obj L)) ∧
  (∃ cMinus cPlus : ℤ, ∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l E n) ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X
        (Padic.coefficientExtensionRing l E n)),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E n) c ⊣ G) →
    ∀ a b : ℤ, a ≤ b → ∀ L, constructibleInterval l E n hn Y a b L →
      constructibleInterval l E n hn X (a + cMinus) (b + cPlus) (G.obj L)) ∧
  ∀ (G : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l E n) ⥤
      AlgebraicGeometry.Scheme.proEtaleDerivedCategory X
        (Padic.coefficientExtensionRing l E n)),
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E n) c ⊣ G) →
    ∀ L, finiteTorConstructible l E n hn Y L → finiteTorConstructible l E n hn X (G.obj L)

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

/-- Admissibility for the condensed ring itself. In particular this applies to
O_E, E, and the finite-subextension-valued algebraic closure with their actual condensed
ring structures. This definition does not test reductions, rationalizations or lattices.
The condensed paragraph specifies ambient adjunctions with refinement coherence and the
two preservation conditions; it does not specify an additional finite-stage FullCD test.
Source: latest blueprint `def-weil-exceptional-adjoint-admissibility`, condensed paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
def IsExceptionalAdjointAdmissibleAtCondensedRing
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  Nonempty (CondensedAmbientExceptionalAdjunctions Λ f) ∧
  (∀ (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))),
    (rightDerivedLowerShriekOfCompactification Λ c ⊣ G) →
    boundedConstructible (condensedRingObj Λ Y) ≤
      (boundedConstructible (condensedRingObj Λ X)).inverseImage G) ∧
  (∃ cMinus cPlus : ℤ, ∀ (G : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))),
    (rightDerivedLowerShriekOfCompactification Λ c ⊣ G) →
    ∀ a b : ℤ, a ≤ b → ∀ L, boundedConstructible (condensedRingObj Λ Y) L →
      DerivedCategory.homologyConcentratedIn a b L →
      boundedConstructible (condensedRingObj Λ X) (G.obj L) ∧
      DerivedCategory.homologyConcentratedIn (a + cMinus) (b + cPlus) (G.obj L)) ∧
  ∀ (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))),
    (rightDerivedLowerShriekOfCompactification Λ c ⊣ G) →
    condensedConstructibleFiniteTor Λ Y ≤ (condensedConstructibleFiniteTor Λ X).inverseImage G

/-- Ambient adjunctions and their coherent comparison isomorphisms over compactifications.
The unit and counit equations use the very same left and right comparison maps;
identity and composition equations express compatibility with refinements.
Source: latest blueprint `def-weil-exceptional-adjoint-admissibility`, condensed paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
structure CondensedAmbientExceptionalAdjunctions
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The ambient right adjoint at each compactification. -/
  right : ∀ _c : Compactification f,
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  /-- The actual adjunctions, hence their units and counits. -/
  adj : ∀ c, rightDerivedLowerShriekOfCompactification Λ c ⊣ right c
  /-- Refinement comparison of left adjoints. -/
  theta : ∀ {c d : Compactification f} (_r : c ⟶ d),
    rightDerivedLowerShriekOfCompactification Λ c ≅ rightDerivedLowerShriekOfCompactification Λ d
  /-- Contravariant comparison of right adjoints. -/
  rho : ∀ {c d : Compactification f} (_r : c ⟶ d), right d ≅ right c
  /-- The refinement square for the units. -/
  unit_compatibility : ∀ {c d : Compactification f} (r : c ⟶ d) K,
    (adj d).unit.app K ≫ (rho r).hom.app
        ((rightDerivedLowerShriekOfCompactification Λ d).obj K) =
      (adj c).unit.app K ≫ (right c).map ((theta r).hom.app K)
  /-- The refinement square for the counits. -/
  counit_compatibility : ∀ {c d : Compactification f} (r : c ⟶ d) L,
    (rightDerivedLowerShriekOfCompactification Λ c).map ((rho r).hom.app L) ≫
        (adj c).counit.app L = (theta r).hom.app ((right d).obj L) ≫ (adj d).counit.app L
  /-- Left comparison along an identity refinement. -/
  theta_id : ∀ c, theta (𝟙 c) = Iso.refl _
  /-- Right comparison along an identity refinement. -/
  rho_id : ∀ c, rho (𝟙 c) = Iso.refl _
  /-- Left comparison along a composite refinement. -/
  theta_comp : ∀ {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e),
    theta (r ≫ s) = theta r ≪≫ theta s
  /-- Right comparison along a composite refinement. -/
  rho_comp : ∀ {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e),
    rho (r ≫ s) = rho s ≪≫ rho r

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
