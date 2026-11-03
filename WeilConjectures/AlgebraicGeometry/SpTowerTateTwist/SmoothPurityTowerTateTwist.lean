/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.Semilinear.QuotientReductionCore
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories

/-! # The canonical Tate twist (d)[2d] on varying-coefficient towers

The integral Tate line O_E(1) of def-coefficient-twists-detailed is made constant in the
level on the sequence site, and its coefficients are extended along the actual constant
quotient maps O_E -> O_E/l^(n+1). This is one strict semilinear system, with levels
B_n tensor O_E(1) and transitions induced by the quotient maps; no comparison family is
chosen. Its d-th tensor power is the tower Tate line of weight d, and the tower twist
is derived tensor with that line in degree zero followed by the shift [2d].
Source: blueprint latest, Local pairs (H_U = e^* p_d^*(-)(d)[2d])
(blueprint: def-sp-tower-tate-twist).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerTateTwist

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual constant quotient maps O_E -> O_E/l^(n+1) are compatible with the actual
adjacent quotient maps of the tower coefficients.
Source: coefficient convention of det-sp-tower-shriek-levels
(blueprint: def-sp-tower-tate-twist).
Proof: both sides are the constant sheaf of the ring map induced by the quotient
O_E -> O_E/l^(n+1); the factorization through O_E/l^(n+2) is the identity on classes. -/
theorem quotient_comp (T : Scheme.{u}) (n : ℕ) :
    spEllTwistQuotient l E T (n + 1) ≫ SpTowerShriek.tau l E T n =
      spEllTwistQuotient l E T n := by
  sorry

/-- The quotient maps as one ring map from the level-constant O_E to the tower ring B_•.
Source: Local pairs, coefficient towers (blueprint: def-sp-tower-tate-twist). -/
def ringMap (T : Scheme.{u}) :
    SemilinearSections.quotientConstantRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (purTwistIntegralConstant T l E) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) :=
  SemilinearSections.quotientRingMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (purTwistIntegralConstant T l E) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (spEllTwistQuotient l E T) (quotient_comp l E T)

/-- The integral Tate line O_E(1) of def-coefficient-twists-detailed, constant in the level.
Source: Local pairs (blueprint: def-sp-tower-tate-twist). -/
def constantLine (T : Scheme.{u}) :
    SemilinearSections.Mod.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (SemilinearSections.quotientConstantRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (purTwistIntegralConstant T l E)) :=
  (SemilinearSections.quotientConstant.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (purTwistIntegralConstant T l E)).obj (purTwistIntegralOne T l E)

/-- The tower Tate line of weight one: the system n ↦ B_n ⊗_{O_E} O_E(1), obtained by the
actual sheafified change of rings along the quotient ring map. Its transitions are those of
the strict system, induced by the quotient maps; no comparison isomorphism is chosen.
Source: Local pairs, finite Tate lines and quotient transitions
(blueprint: def-sp-tower-tate-twist). -/
def lineOne (T : Scheme.{u}) : SpTowerShriek.S l E T :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (ringMap l E T) (constantLine l E T)

/-- The tower Tate line of weight d ≥ 0: the d-th tensor power of lineOne on the sequence
site, with the unit system in weight zero (the published scalarTensorPower convention).
Source: Local pairs, Tate twist (d) (blueprint: def-sp-tower-tate-twist). -/
def line (T : Scheme.{u}) (d : ℕ) : SpTowerShriek.S l E T :=
  SheafOfModules.scalarTensorPower
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)) (lineOne l E T) d

/-- The tower Tate twist K ↦ K(d): the recorded K-flat derived tensor of the ordinary tower
category with the weight-d line in degree zero. This is the defining formula of
SpChartAdmissibility.twist, with the canonical line in place of a supplied Twists datum.
Source: Local pairs, H_U before the shift (blueprint: def-sp-tower-tate-twist). -/
def twist (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (d : ℕ) :
    SpTowerShriek.D l E T ⥤ SpTowerShriek.D l E T :=
  Functor.prod' (𝟭 _) ((Functor.const _).obj
      ((DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).obj (line l E T d))) ⋙
    SpTowerShriek.tensor l E b T

/-- The tower Tate twist with shift, K ↦ K(d)[2d].
Source: Local pairs, H_U = e^* p_d^*(-)(d)[2d] (blueprint: def-sp-tower-tate-twist). -/
def twistShift (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (d : ℕ) :
    SpTowerShriek.D l E T ⥤ SpTowerShriek.D l E T :=
  twist l E b T d ⋙ shiftFunctor (SpTowerShriek.D l E T) (2 * (d : ℤ))

/-! ## Comparisons (statements only) -/

/-- Each level of the canonical tower line is the finite signed Tate line of
def-sp-ell-twist-quotient-data, i.e. the coefficientTwistLine of
def-coefficient-twists-detailed over B_n.
Source: Local pairs (blueprint: def-sp-tower-tate-twist).
Proof: evaluation is restriction to the level-n slice, which commutes with sheafified
change of rings and with sheaf tensor products; on the slice the constant line is
O_E(1) and the ring map is the quotient map q_n. -/
theorem line_level (T : Scheme.{u}) (n d : ℕ) :
    Nonempty ((SpTowerShriek.ev l E T n).obj (line l E T d) ≅
      spEllTwistLine l E T n (d : ℤ)) := by
  sorry

/-- The canonical line is a Twists datum: there are normalized quotient comparisons and
level identifications under which its actual strict transitions are the specified root
transitions. Hence it is accepted by every statement quantified over Twists.
Source: Local pairs (blueprint: def-sp-tower-tate-twist).
Proof: the normalized comparisons are the composite change-of-rings isomorphisms, which
are compatible with tensor powers and, the lines being invertible, with duals; the level
identifications are those of line_level, and both transitions are induced by tau_n. -/
theorem exists_twists (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)] :
    ∃ w : SpChartAdmissibility.Twists l E T, w.tower = line l E T := by
  sorry

/-- For every Twists datum whose towers are the canonical lines, the chart twist of
SpChartAdmissibility is literally the canonical tower twist.
Source: Local pairs (blueprint: def-sp-tower-tate-twist).
Proof: unfold the two definitions and rewrite by the equality of towers. -/
theorem chart_twist_eq (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    (w : SpChartAdmissibility.Twists l E T) (hw : w.tower = line l E T)
    (K : SpTowerShriek.D l E T) (r : ℕ) :
    SpChartAdmissibility.twist l E b w K r = (twist l E b T r).obj K := by
  sorry

/-- The canonical lines give a TwistFamily over every field in which l is a unit, whose
towers are the canonical lines on every k-scheme.
Source: Local pairs (blueprint: def-sp-tower-tate-twist).
Proof: apply exists_twists on each k-scheme; l is invertible in every residue field. -/
theorem exists_twistFamily {k : Type u} [Field k] (hl : IsUnit (l : k)) :
    ∃ w : SpCoordinateAdjunction.TwistFamily l E k,
      ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))], (w T).tower = line l E T := by
  sorry

/-- Levelwise, the tower twist is the finite twist of def-coefficient-twists-detailed:
evaluation at level n of K(d)[2d] is (Ev_n K) ⊗ L_{n,d} shifted by 2d.
Source: Local pairs, levelwise Tate twists (blueprint: def-sp-tower-tate-twist).
Proof: evaluation is compatible with the recorded K-flat tensor (tensor evaluation of
the semilinear calculus) and with shifts; the line is flat, so the derived tensor at
level n is the ordinary tensor with its level, identified by line_level. -/
theorem twistShift_level (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (n d : ℕ)
    [(spEllTwistOne l E T n).IsFiniteLocallyFreeOfRank 1] (K : SpTowerShriek.D l E T) :
    letI := (coefficientTwistLine_exact T (spEllTwistOne l E T n) (d : ℤ)).1
    letI := (coefficientTwistLine_exact T (spEllTwistOne l E T n) (d : ℤ)).2.1
    letI := (coefficientTwistLine_exact T (spEllTwistOne l E T n) (d : ℤ)).2.2
    Nonempty ((SpTowerShriek.Ev l E T n).obj ((twistShift l E b T d).obj K) ≅
      ((SemilinearSections.derivedExact.{u + 1, u, u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T n) (SpTowerShriek.B l E T n)
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
          (A := SpTowerShriek.B l E T n)
          (coefficientTwistLine T (spEllTwistOne l E T n) (d : ℤ)))).obj
        ((SpTowerShriek.Ev l E T n).obj K))⟦2 * (d : ℤ)⟧) := by
  sorry

/-- Weight zero is the identity. Source: Local pairs, d = 0
(blueprint: def-sp-tower-tate-twist).
Proof: the weight-zero line is the unit system and the shift is by zero. -/
theorem twistShift_zero (b : SpTowerShriek.Base l E) (T : Scheme.{u}) :
    Nonempty (twistShift l E b T 0 ≅ 𝟭 _) := by
  sorry

/-- Twists compose additively, as used by the ordered affine iteration.
Source: Local pairs, ordered coordinates (blueprint: def-sp-tower-tate-twist).
Proof: associativity of the K-flat tensor, the tensor-power product of lines, and
compatibility of tensor with shifts. -/
theorem twistShift_add (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (d e : ℕ) :
    Nonempty (twistShift l E b T d ⋙ twistShift l E b T e ≅ twistShift l E b T (d + e)) := by
  sorry

/-- Uniformity: the twist preserves the level bounds of def-sp-chart-tate-tower-data and
moves cohomological support and Tor amplitude down by 2d.
Source: Uniformity (blueprint: def-sp-tower-tate-twist).
Proof: tensor with an invertible line is exact and preserves constructibility and Tor
amplitude levelwise (twistShift_level); the shift moves both intervals by 2d. -/
theorem twistShift_bounds (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (K : SpTowerShriek.D l E T) (d : ℕ)
    (a c s t : ℤ) (hK : SpChartAdmissibility.bounds l E T K a c s t) :
    SpChartAdmissibility.bounds l E T ((twistShift l E b T d).obj K)
      (a - 2 * (d : ℤ)) (c - 2 * (d : ℤ)) (s - 2 * (d : ℤ)) (t - 2 * (d : ℤ)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerTateTwist
