/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCoefficientTwists
import Mathlib.Data.Nat.Prime.Infinite

/-! # Intrinsic coefficient twists without an auxiliary finite field

Source: blueprint main-20261015, coefficient twists, order 1864
(blueprint: def-coefficient-twists-detailed).

The signed lines, exact tensor, rational tensor and common-stage tensor are the
published constructions. These interfaces remove only the unused finite-field
proof parameters from the completed line and its field images. The previously
recorded interfaces of this node (the intrinsic, fixed finite positive and PBC
coordinate twists) remain publicly imported.

## Main definitions
* `sfIntegralTwistingObject`
* `sfIntegralTwistingFunctor`
* `sfRationalTwistingFunctor`
* `sfQbarTwistingFunctor`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The published completed signed line in degree zero, with no finite-field datum.
Source: blueprint coefficient twists, integral paragraph
(blueprint: def-coefficient-twists-detailed). -/
abbrev sfIntegralTwistingObject (m : ℤ) : DerivedCategory (scalarReductionSource l E S) :=
  (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E S m)

/-- Intrinsic membership of the published completed signed line.
Source: blueprint coefficient twists, integral paragraph
(blueprint: def-coefficient-twists-detailed).
Proof: the root tower supplies the completed rank-one first line and its finite
reductions. Trivialize that line on a pro-etale cover. Every tensor power and
internal dual is the coefficient unit there; reduction of powers commutes with
this trivialization, and reduction of the dual is characterized by evaluation.
Thus all positive reductions are finite locally constant in degree zero, with
one support interval [0,0]. The compatible root tower recovers the completed
line; tensor by a rank-one line preserves products, so the canonical reduction
units give its distinguished augmented Roos triangle. These are exactly
IsSfDerivedComplete and the uniform constructible-reduction clauses of
sfIntegralConstructible. No characteristic or structure map of S is used. -/
theorem sfIntegralTwistingObject_mem (m : ℤ) :
    sfIntegralConstructible l E S (sfIntegralTwistingObject l E S m) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  exact intrinsicIntegralCoefficientTwist_mem D l hl E S m

/-- The same signed line as an object of the recorded intrinsic full subcategory.
Source: blueprint coefficient twists, integral paragraph
(blueprint: def-coefficient-twists-detailed). -/
def sfIntegralTwistingCoefficient (m : ℤ) : sfIntegralConstructibleCategory l E S :=
  ⟨sfIntegralTwistingObject l E S m, sfIntegralTwistingObject_mem l E S m⟩

/-- The recorded exact tensor on completed module sheaves, descended termwise.
Source: blueprint coefficient twists, formula K(m)
(blueprint: def-coefficient-twists-detailed). -/
abbrev sfIntegralTwistingFunctor (m : ℤ) :=
  (integralSheafTwist l E S m).mapDerivedCategory

/-- The image of the signed integral line under the recorded raw rationalization.
Source: blueprint coefficient twists, rational paragraph
(blueprint: def-coefficient-twists-detailed). -/
def sfRationalTwistingCoefficient (m : ℤ) : sfRationalConstructibleCategory l E S :=
  (sfRationalConstructibleLocalization l E S).obj (sfIntegralTwistingCoefficient l E S m)

/-- Tensor by that image, using the unique bilinear intrinsic rational tensor.
Objects are the integral tensor representatives; localized arrows are sent by
(a tensor f, b tensor g) to ab tensor (f tensor g), as specified by rationalDerivedTensor.
Source: blueprint coefficient twists, formula K(m)
(blueprint: def-coefficient-twists-detailed). -/
def sfRationalTwistingFunctor (m : ℤ) :
    sfRationalConstructibleCategory l E S ⥤ sfRationalConstructibleCategory l E S :=
  (𝟭 (sfRationalConstructibleCategory l E S)).prod'
    ((Functor.const (sfRationalConstructibleCategory l E S)).obj
      (sfRationalTwistingCoefficient l E S m)) ⋙ rationalDerivedTensor l E S

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The same line represented at the least finite coefficient stage.
Source: blueprint coefficient twists, common-stage paragraph
(blueprint: def-coefficient-twists-detailed). -/
def sfQbarTwistingCoefficient (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω S :=
  ⟨Padic.finiteCoefficientBase l Ω,
    sfRationalTwistingCoefficient l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) S m⟩

/-- The recorded common-stage tensor with the same signed line. Its arrows and
scalar comparisons are exactly those of commonStageDerivedTensor.
Source: blueprint coefficient twists, formula K(m)
(blueprint: def-coefficient-twists-detailed). -/
def sfQbarTwistingFunctor (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω S ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω S :=
  (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω S)).prod'
    ((Functor.const (generalAlgebraicallyClosedConstructibleCategory l Ω S)).obj
      (sfQbarTwistingCoefficient l S Ω m)) ⋙ commonStageDerivedTensor l Ω S

end WeilConjectures
