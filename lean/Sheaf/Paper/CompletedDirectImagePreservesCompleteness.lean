/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.CompletedCoefficientPushforwardModels

/-! # Derived direct image preserves completed-coefficient completeness

Source: Stacks proetale.tex Tag 099N (3),(4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized direct image along the canonical finite-projection structural
map preserves derived completeness, independently of choices of total derived model.

Source: Stacks proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case (3),(4)
(blueprint: lem-pur-completed-direct-image-preserves-completeness).
Proof:
1. The coefficient integers form a complete discrete valuation ring. Its uniformizer
is a nonzero nonunit, every positive-power quotient is finite, and the two-term free
resolution makes each quotient perfect. The canonical map from the integers to the
inverse limit of these quotients is an isomorphism. These are the hypotheses of the
adic direct-image proposition with the principal uniformizer ideal.
2. The finite constant coefficient inverse-image identifications and the equalities
hc identify the structural map c with the completed structural map in that proposition.
Transport its module functor across the coefficient and small-site equivalences.
The K-injective unit equation identifies the resulting derived direct image with F.
3. The adic direct-image proposition preserves intrinsic completeness: its normalized
completion unit is direct image of the source completion unit followed by the
canonical direct-image/inverse-limit comparison, both invertible. Apply the
Roos/intrinsic completeness equivalence on source and target to identify this with
IsDerivedCompleteUnrestricted. Invariance under the normalized derived comparison
from step 2 gives the assertion for F. All positive exponents and quotient transitions
are retained; no constructibility, boundedness or properness assumption is needed.
The same argument covers an empty source or target and the zero object. -/
theorem directImage_preservesComplete (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    [hpush : (push f c).Additive] (F : RightImage (push f c))
    (K : DerivedCategory (Mod X (R l E X)))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E Y (F.functor.obj K) := by
  sorry

end WeilConjectures.CompletedCoefficientPushforward
