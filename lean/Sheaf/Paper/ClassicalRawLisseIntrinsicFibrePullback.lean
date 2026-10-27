/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.ClassicalRawLisseRealizationData

/-! # Completed pullback and intrinsic adic fibres -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Intrinsic adic fibres commute with the actual completed rational pullback.
Source: Bhatt--Scholze, Remark 6.8.15; the normalized adic-heart pullback comparison
(blueprint: lem-zl-classical-raw-lisse-intrinsic-fibre-pullback).

Proof: In the completed coefficient presentation, use the adic-heart pullback-fibre
comparison, whose integral map is the composition of the specified completed
pullbacks followed by H0, point sections, and localization. Transport it along the
constant-section-normalized coefficient equivalence to the intrinsic sf category.
The normalized integral pullback comparison identifies its underlying finite tower
with that of rationalDerivedPullback. The composition equations identify successive
pullback to x then f with pullback to x followed by f. Descend the resulting natural
isomorphism and its inverse through raw scalar localization; each fraction acts by
the same inverse-uniformizer scalar on both sides. Thus the comparison holds on the
whole raw category, not merely its heart. No nonempty or positive-rank hypothesis
is used. -/
theorem classical_raw_lisse_intrinsic_fibre_pullback
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (x : Spec (.of D.k) ⟶ V.scheme) :
    Nonempty (@rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
      (baseInvertible D l hl V) (baseInvertible D l hl W) ⋙
      sfAdicRationalFiber l E V.scheme x ≅ sfAdicRationalFiber l E W.scheme (x ≫ f)) := by
  sorry

end WeilConjectures.ClassicalRawLisse
