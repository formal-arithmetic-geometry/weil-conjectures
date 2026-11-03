/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.Refinement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Sf.SfFullCohomologicalDimension
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Exceptional-adjoint admissibility at a finite coefficient stage

Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-def-sf-admissible/_section.md`, order 1702 (blueprint: sk-def-sf-admissible).

The ambient condition is only the existence of a full cohomological-dimension bound.
Admissibility additionally requires preservation of bounded constructibility, uniform
signed interval shifts, and finite Tor amplitude by every right adjoint of the candidate
attached to the specified compactification. These are predicates, not automatic hypotheses.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The ambient exceptional right adjoint datum at the positive finite coefficient stage:
a nonnegative FullCD bound for the proper part of the chosen compactification. The
predicate is defined on any compactified morphism; admissibility below restricts it to
the finite-field setting. FullCD quantifies over all source module sheaves and their
restrictions to every pro-etale base change, without a finiteness condition on that
site object. Existence of a right adjoint is a consequence, not an extra defining clause.
Source: main-20261015, `sk-def-sf-admissible/_section.md`, clause (1), order 1702
(blueprint: sk-def-sf-admissible). -/
noncomputable def HasSfAmbientExceptionalDatum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∃ cCD : ℕ, sfFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E n) cCD

end WeilConjectures
