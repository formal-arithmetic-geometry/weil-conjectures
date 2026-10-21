/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.GeoP1Cohomology
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-!
# Canonical projective-line decomposition and trace systems

Source: blueprint main-20261015, det-sp-p1-trace, clauses 1--2 and the
arbitrary-base consequence (blueprint: def-sp-p1-proetale-trace-system).

## Main definitions

- `SpP1BaseTraceConditions` specifies the unit, Kummer, exchange and normalization
  equations for families of projective-line decompositions and their traces.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The Chern arrows over all bases; their Kummer normalization is a clause of the
statement, rather than an assumption or a choice of generators.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1ChernFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1ChernFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
            (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) := ⟨SpP1ChernFamily.map⟩

/-- A family of twisted isomorphisms; their two components are fixed
in the statement. The trace is always the existing `geoP1Trace`.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1TwistedFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
        (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
          (geoP1Twist A N hA (ProjectiveLine S) 1 2)

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1TwistedFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
            (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
              (geoP1Twist A N hA (ProjectiveLine S) 1 2)) := ⟨SpP1TwistedFamily.map⟩

/-- The untwisted decomposition arrows on all bases.
Source: det-sp-p1-trace, clause 1 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1DecompositionFamily (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
        (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1DecompositionFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
            (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
              (geoP1Unit A (ProjectiveLine S))) := ⟨SpP1DecompositionFamily.map⟩

/-- The canonical comparison image of the twisted adjunction unit.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
def geoP1TwistedUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    geoP1Twist A N hA S 1 2 ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  (geoP1Comparison A S).map
    (Etale.ordinaryFiniteP1Unit A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) S hS) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The canonical comparison image of the Chern adjunct.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
def geoP1ChernPushforward (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (c : Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    geoP1Unit A S ⟶ (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  (geoP1Comparison A S).map (Etale.ordinaryFiniteP1ChernPushforward A N hA S c) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The five normalization conditions, kept abstract for kernel sharing.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1NormalizationClauses (p q r s t : Prop) : Prop where
  chern : p
  decomposition_iso : q
  decomposition_eq : r
  twisted_unit : s
  twisted_chern : t

/-- The five canonical normalization clauses over a single base.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1NormalizedAt (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  SpP1NormalizationClauses
    (Etale.ordinaryFiniteP1ChernSpec A N hA S
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
          hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS))
    (IsIso (d S hS))
    (HEq (d S hS)
        (geoP1SumComparison A S (Etale.ordinaryFiniteUnit A S)
            (Etale.p1DecompositionTwist A N hA S (-1) (-2)) ≫
            (geoP1Comparison A S).map (Etale.p1DecompositionMap A N hN hA S hS (c S hS)) ≫
            geoP1PushComparison A (ProjectiveLine S ↘ S)
              (Etale.ordinaryFiniteUnit A (ProjectiveLine S))))
    (HEq (biprod.inl ≫ (b S hS).hom) (geoP1TwistedUnit A N hN hA S hS))
    (HEq (biprod.inr ≫ (b S hS).hom)
    (geoP1ChernPushforward A N hA S (c S hS)))

/-- The exact unit-and-Kummer formula, its invertibility, and the twisted components.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1NormalizedDecompositions (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    SpP1NormalizedAt A N hN hA c b d S hS

/-- Both canonical base-change squares, with no Noetherian or flatness restriction.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1BaseChange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) (d : SpP1DecompositionFamily A N hA) : Prop :=
  ∀ (S' S : Scheme.{u}) (g : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    HEq ((geoP1Pullback A g).map (d S hS) ≫ geoP1UnitExchange A g)
      (geoP1SourceMap A N hN hA g hS ≫ d S' hS') ∧
    HEq ((geoP1Pullback A g).map (geoP1Trace A N hA S (b S hS)) ≫
        (geoP1UnitPullback A g).hom)
      (geoP1TwistExchange A N hN hA g hS ≫ geoP1Trace A N hA S' (b S' hS'))

/-- The hyperplane component integrates to one. Its component is fixed above.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1TraceChern (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (b : SpP1TwistedFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    HEq (biprod.inr ≫ (b S hS).hom ≫ geoP1Trace A N hA S (b S hS))
      (𝟙 (geoP1Unit A S))

/-- Every geometric rational point has the same Kummer class as O(1).
Source: det-sp-p1-trace, clauses 1--3 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1RationalPointChern (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (c : SpP1ChernFamily A N hA) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (hΩ : IsUnit (N : Γ(Spec (.of Ω), ⊤)))
    (x : Spec (.of Ω) ⟶ ProjectiveLine (Spec (.of Ω)))
    (_hx : x ≫ (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) = 𝟙 _),
    ∃ hI : x.ker.IsInvertible,
      HEq (Etale.ordinaryFiniteClass A (ProjectiveLine (Spec (.of Ω)))
          (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec (.of Ω))) N A hA) 2
          (c (Spec (.of Ω)) hΩ))
        (Etale.supportedKummerChern A N hA x hI
          ((map_natCast (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)).appTop.hom N) ▸
            hΩ.map (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)).appTop.hom))

/-- The canonical Kummer-normalized projective-line systems over all bases.
This is a predicate on the displayed families, not a choice of any arrow.
Source: det-sp-p1-trace, clauses 1--2 and final paragraph
(blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1BaseTraceConditions (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) : Prop :=
  SpP1NormalizedDecompositions A N hN hA c b d ∧
  SpP1BaseChange A N hN hA b d ∧
  SpP1TraceChern A N hA b ∧
  SpP1RationalPointChern A N hA c

end AlgebraicGeometry.ProEtale
