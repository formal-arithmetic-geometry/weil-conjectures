/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData

/-! Existence of normalized ordinary quotient-coordinate comparisons.

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint
lem-route-ordinary-exists-unique, first construction step.
(blueprint: lem-route-ordinary-existence)

The proof constructs the two direct-image comparisons sectionwise from the supplied
right-evaluation and right-underlying isomorphisms, then transports the two inverse
and extension comparisons through the ordinary adjunctions. The section identities,
transition squares, and mate equations are checked before assembling the record.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- The normalized ordinary comparison record exists.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10;
construction steps of lem-route-ordinary-exists-unique.
(blueprint: lem-route-ordinary-existence)

Proof: for each of the open and proper maps, let e identify the sections of the
coordinate image of sequence direct image with direct image of the coordinate
sections. The sequence-site evaluation and quotient ring isomorphisms give e;
its section functions send each residue class to itself. Let b be rightEvaluation
followed by rightUnderlying for the supplied ordinary image. The ordinary right
section laws show that b preserves addition, zero, scalar action and the adjacent
transitions. Thus b inverse followed by e in functional order gives a linear
isomorphism at each level. Their transition squares and naturality follow after
postcomposing with b, which is invertible. They assemble to openPush and properPush
with the required section normalizations.

Conjugate the ordinary inverse/direct adjunctions along the coordinate equivalences.
The openPush comparison identifies their right adjoints. Uniqueness of left adjoints
therefore supplies openPull; its defining Hom bijection is openPull_transpose. Next
conjugate the two extension/inverse adjunctions. Identify their right adjoints using
openPull and apply left-adjoint uniqueness again, giving openExtension and its
transpose equation. Assemble these four isomorphisms and their equations. The
argument uses no invertibility of system transitions and includes empty schemes
and zero modules. -/
theorem ordinary_exists : Nonempty (Ordinary l E S G H D) := by
  sorry

end WeilConjectures.PurIntegralSupportComparison
