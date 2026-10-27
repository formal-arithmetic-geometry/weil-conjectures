/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.TwistedPullbackTowerDomainDefinitions

/-! # Pullback and ordered shifted Tate-line bounds -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

/-- The finite pullback and shifted Tate-line bounds, before choosing an orientation.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2); tower-domain steps 2--4.
(blueprint: lem-sp-pullback-ordered-tate-bounds)

Proof: finite type over the field makes X and Y Noetherian and qcqs. Smooth pullback
is finite type. At each positive coefficient quotient, apply pullback Tor stability
after transport along the equality of ell-power and ramification-indexed uniformizer
ideals. Test its Tor interval against the coefficient unit to obtain [a,z] for
cohomology. The integral Tate line is locally free of rank one; scalar extension to
the ell-power quotient preserves its local trivializations. Its d-th tensor power
is again locally free of rank one with finite constant local models, including the
unit at d=0. Hence tensoring it is exact and preserves constructible strata.
Induct on the ordered tensor definition: each shifted degree-one factor changes
both cohomological and Tor endpoints by -2. The same local calculation with the
line on the left gives the reversed tensor bounds; it does not require a chosen
symmetry on the abstract tower tensor. Tensor associativity computes every
Tor test by tensoring its degree-zero test module with the unshifted flat line.
This proves [a-2d,z-2d] for P, and [-2d,-2d] for the ordered coefficient line by
the same induction starting from the unit. No normalization is imposed on K.
On the empty scheme all cohomology sheaves vanish, so the same intervals apply. -/
theorem pullback_ordered_tate_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (w : SpChartAdmissibility.Twists l E X.left)
    (K : SpTowerCalculus.C l E b q Y.left) (a z : ℤ) (haz : a ≤ z)
    (hTor : ∀ n : ℕ, HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
      ((SpTowerShriek.Ev l E Y.left n).obj
        ((SpTowerGamma.realization l E b q Y.left).obj K)) a z) :
    SpChartAdmissibility.bounds l E X.left (B l E b o q f.left K) a z a z ∧
    (∀ n : ℕ,
      IsConstructibleProEtaleModuleSheaf X.left (SpTowerShriek.R l E n)
        (spEllTwistLine l E X.left n (d : ℤ)) ∧
      (spEllTwistLine l E X.left n (d : ℤ)).IsFiniteLocallyFreeOfRank 1 ∧
      (d = 0 → Nonempty (spEllTwistLine l E X.left n (d : ℤ) ≅
        SheafOfModules.unit ((sheafCompose (ProEt.topology X.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (SpTowerShriek.B l E X.left n))))) ∧
    SpChartAdmissibility.bounds l E X.left (P l E b o q f.left w d K)
      (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d) ∧
    SpChartAdmissibility.bounds l E X.left (SpTowerGamma.orderedLine l E b X.left w d)
      (-2 * d) (-2 * d) (-2 * d) (-2 * d) ∧
    SpChartAdmissibility.bounds l E X.left
      ((SpTowerShriek.tensor l E b X.left).obj
        (SpTowerGamma.orderedLine l E b X.left w d, B l E b o q f.left K))
      (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d) := by sorry

end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain
