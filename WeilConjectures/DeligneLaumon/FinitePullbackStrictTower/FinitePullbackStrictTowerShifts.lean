/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerRepresentative

/-! # Shifts of the normalized strict finite tower comparison
Source: Stacks 05SE, 06XN, 0FNH.
(blueprint: lem-a1-finite-pullback-strict-tower-shifts).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The fixed balanced and Koszul zigzag respects the canonical integer shifts.
Source: Stacks Project, more-algebra.tex Tag 0FNH; derived.tex Tags 05SE and 06XN.
(blueprint: lem-a1-finite-pullback-strict-tower-shifts).

Proof: reduction and finite pullback act termwise by additive module functors.
Their standard shift comparisons are identities on reindexed terms, commute
with every quotient transition, and satisfy the zero and addition equations.
Apply rightKanExtension_coherentShift to these chain functors followed by Q
and their universal derived counits. Apply it also to termwise tower pullback.
The resulting counit squares are the three ShiftDescent assertions. On a good
representative P the reduction and tower counits are invertible. The two Koszul
basis formulas identify the tensor comparison uniquely: in degrees -1 and 0,
shifting P introduces no exchange of factors, so the first-variable total tensor
shift is unsigned. The balanced formula is likewise unchanged by reindexing.
The augmentation has degree zero and commutes with these same shifts. Thus the
specified zigzag intertwines the composite reduction/pullback shift and the
finite shift. Cancel the counits in its defining equation to obtain the b square
on good representatives. Every derived object has a flat-term K-flat resolution;
naturality transports the square along that representative isomorphism. This
proves the square for every object and integer, including negative shifts. -/
theorem finite_pullback_strict_tower_shifts
    (C : RepresentativeComparison l E g) : Nonempty (ShiftData l E g C) := by sorry

end WeilConjectures.FinitePullbackStrictTower
