/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates
import Sheaf.Paper.CoefficientTowerShriekCalculus

/-! # Binary coefficient-tower counit gluing steps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₀ v₁ w₀ w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerBinaryCounit

open SpTowerShriek SpTowerBinaryCtfFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b) (q : SpTowerCalculus.Coordinates l E b)

/-- Open restriction preserves a local representing pair, with its specified nested counit.
Source: blueprint latest, smooth tower geometric gluing, Gluing paragraph, restriction
of local pairs (blueprint: lem-sp-tower-restricted-representing-pair).

Proof: exact restriction preserves the uniform cohomological and Tor intervals and
intrinsic constructibility. For a good test N on D contained in U, exact open extension
inside U preserves goodness. Compose the inverse open-adjunction Hom equivalence with
hU on this extended test. Open composition identifies the resulting compact support with
support D. Naturality and the counit formula identify the composite bijection with
b ↦ support D(b) followed by restrictedCounit. The nested map is exactly the mate of
the restricted unit under restrictionComp, so these identifications use the displayed
counit, including for an empty open and for D = U. -/
theorem restricted_representing_pair
    (p : ℕ) (hp : 0 < p) (hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (Z Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : Z ⟶ Y) (c₀ : Compactification h.left)
    (U : Z.left.Opens) (K : D l E Y.left) (P : D l E U.toScheme)
    (hP : good l E b q U.toScheme P)
    (eU : (support l E b o c₀ U).obj P ⟶ K)
    (hU : Represents l E b q (support l E b o c₀ U) P K eU) :
    (∀ (D₀ : Z.left.Opens) (i : D₀ ≤ U),
      good l E b q D₀.toScheme ((restrictionBetween l E b o i).obj P) ∧
      Represents l E b q (support l E b o c₀ D₀)
        ((restrictionBetween l E b o i).obj P) K
        (restrictedCounit l E b o c₀ i P K eU)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerBinaryCounit
