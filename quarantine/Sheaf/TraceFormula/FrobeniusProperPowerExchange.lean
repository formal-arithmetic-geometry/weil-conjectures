/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.CondensedAmbientExchange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Proper Frobenius power squares and their canonical mates

Source: Stacks Project, sites-cohomology.tex, Tag 0E47,
remark-compose-base-change-horizontal, and Tag 0D6D; Deligne, Weil II (1.1.10)--(1.1.11)
(blueprint: lem-trf-frobenius-proper-power-exchange).

The helpers specialize the published constant-ring operations and canonical compositors.
The exchange is the unit--square--counit mate, in ordinary unbounded derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusProperPower

variable (D : FiniteFieldDatum.{u})
  (W₀ : Over (Spec (.of D.k₀))) [IsProper W₀.hom]

/-- The actual power of id × Spec of geometric field Frobenius on the geometric fibre.
Source: Deligne, Weil II (1.1.10)--(1.1.11)
(blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev middle (r : ℕ) : End (D.geometricFiber W₀).left :=
  End.of (D.geometricGaloisFrobenius W₀) ^ r

/-- The actual power of Spec of geometric field Frobenius on s = Spec k.
Source: Deligne, Weil II (1.1.10)--(1.1.11)
(blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev base (r : ℕ) : End (Spec (.of D.k)) :=
  End.of (frobeniusPointIso D).hom ^ r

/-- Positive power squares commute, are Cartesian, and have isomorphic horizontal arrows.
Source: Stacks 0E47; Deligne, Weil II (1.1.10)--(1.1.11)
(blueprint: lem-trf-frobenius-proper-power-exchange).
Proof (node step 1): lem-weil-frobenius-square-cartesian gives the one-step
isomorphisms and commutation. Induction gives p b^r = h^r p. In the fibre product
P = W ×_(p,s,h^r) s the specified lift is a = (b^r,p). Its inverse is
b^(-r) pi_W: commutation and the pullback relation give p b^(-r) pi_W = pi_s.
The composite with a is the identity on W; the other composite has both projections
identical to those of P, hence is the identity by def-pc-fibre-product.
Powers of the one-step inverses give inverse horizontal maps. No k-linearity is used. -/
theorem geometry (r : ℕ) (_hr : 1 ≤ r) :
    IsPullback (middle D W₀ r) (D.geometricFiber W₀).hom
      (D.geometricFiber W₀).hom (base D r) ∧
    IsIso (middle D W₀ r) ∧ IsIso (base D r) := by
  sorry

/-- The chosen Cartesian identification has forward map precisely the lift (b^r,p).
The canonical IsPullback identification is determined by its two projection equations.
Source: Stacks 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def square (r : ℕ) (hr : 1 ≤ r) :
    ChosenCartesianSquare (middle D W₀ r) (D.geometricFiber W₀).hom
      (D.geometricFiber W₀).hom (base D r) where
  toCommSq := (geometry D W₀ r hr).1.toCommSq
  isoPullback := (geometry D W₀ r hr).1.isoPullback
  hom_fst := (geometry D W₀ r hr).1.isoPullback_hom_fst
  hom_snd := (geometry D W₀ r hr).1.isoPullback_hom_snd

variable (A : Type u) [CommRing A]

/-- B_r = L(b^r)^*, using the existing geometric Galois derived pullback.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev B (r : ℕ) := D.geometricGaloisDerivedPullback W₀ A r

/-- Q_r = L(h^r)^*, with the canonical constant-section coefficient identification.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev Q (r : ℕ) := proEtaleConstantRingDerivedPullback A (base D r)

/-- L = Lp^* on the ordinary unbounded constant-coefficient derived categories.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev L := proEtaleConstantRingDerivedPullback A (D.geometricFiber W₀).hom

/-- R = Rp_* with the canonical adjoint constant-section coefficient action.
Source: Stacks 07A6 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev R := proEtaleRingDerivedDirectImage (D.geometricFiber W₀).hom
  (proEtaleConstantRing (Spec (.of D.k)) A)
  (proEtaleConstantRing (D.geometricFiber W₀).left A)
  (proEtaleConstantRingComparison (D.geometricFiber W₀).hom A)

/-- The canonical inverse composition comparison, transported along the power equality.
This specializes the published K-flat-normalized comparison, with no new choice.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def powerStep {T : Scheme.{u}} (f : End T) (m : ℕ) :
    proEtaleConstantRingDerivedPullback A (f ^ m) ⋙
        proEtaleConstantRingDerivedPullback A (f ^ 1) ≅
      proEtaleConstantRingDerivedPullback A (f ^ (m + 1)) :=
  Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A (f ^ m))
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_one f))) ≪≫
    proEtaleConstantRingPullbackComposition f (f ^ m) A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_succ f m).symm)

/-- t_m: Q_1 Q_m ≅ Q_(m+1), with functor composition written in Lean's order.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev t (m : ℕ) : Q D A m ⋙ Q D A 1 ≅ Q D A (m + 1) :=
  powerStep A (End.of (frobeniusPointIso D).hom) m

/-- d_m: B_1 B_m ≅ B_(m+1), with the same canonical power transport as t_m.
Source: Stacks 0D6D (blueprint: lem-trf-frobenius-proper-power-exchange). -/
abbrev d (m : ℕ) : B D W₀ A m ⋙ B D W₀ A 1 ≅ B D W₀ A (m + 1) :=
  powerStep A (End.of (D.geometricGaloisFrobenius W₀)) m

/-- The specified square comparison theta_r, built from canonical pullback compositors.
Source: Stacks 0D6D and 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def theta (r : ℕ) (hr : 1 ≤ r) : Q D A r ⋙ L D W₀ A ≅ L D W₀ A ⋙ B D W₀ A r :=
  proEtaleConstantRingPullbackComposition (D.geometricFiber W₀).hom (base D r) A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
      (square D W₀ r hr).w.symm) ≪≫
    (proEtaleConstantRingPullbackComposition (middle D W₀ r)
      (D.geometricFiber W₀).hom A).symm

/-- The specified ambient exchange u_r, obtained by the actual unit--square--counit mate.
It is defined on every object and morphism of the ordinary ambient derived category.
Source: Stacks 07A7 and 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def exchange (r : ℕ) (hr : 1 ≤ r) : R D W₀ A ⋙ Q D A r ⟶ B D W₀ A r ⋙ R D W₀ A :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction (D.geometricFiber W₀).hom
      (proEtaleConstantRing (Spec (.of D.k)) A)
      (proEtaleConstantRing (D.geometricFiber W₀).left A)
      (proEtaleConstantRingComparison (D.geometricFiber W₀).hom A))
    (proEtaleRingDerivedAdjunction (D.geometricFiber W₀).hom
      (proEtaleConstantRing (Spec (.of D.k)) A)
      (proEtaleConstantRing (D.geometricFiber W₀).left A)
      (proEtaleConstantRingComparison (D.geometricFiber W₀).hom A))
    (TwoSquare.mk _ _ _ _ (theta D W₀ A r hr).hom)).natTrans

/-- The left side theta_(m+1) L(t_m), as a natural transformation.
Source: Stacks 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def squareLeft (m : ℕ) :
    (Q D A m ⋙ Q D A 1) ⋙ L D W₀ A ⟶ L D W₀ A ⋙ B D W₀ A (m + 1) :=
  Functor.whiskerRight (t D A m).hom (L D W₀ A) ≫
    (theta D W₀ A (m + 1) (Nat.succ_le_succ (Nat.zero_le m))).hom

/-- The right side (d_m L)(B_1 theta_m)(theta_1 Q_m), with explicit associators.
Source: Stacks 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def squareRight (m : ℕ) (hm : 1 ≤ m) :
    (Q D A m ⋙ Q D A 1) ⋙ L D W₀ A ⟶ L D W₀ A ⋙ B D W₀ A (m + 1) :=
  (Functor.associator (Q D A m) (Q D A 1) (L D W₀ A)).hom ≫
    Functor.whiskerLeft (Q D A m) (theta D W₀ A 1 (Nat.le_refl 1)).hom ≫
    (Functor.associator (Q D A m) (L D W₀ A) (B D W₀ A 1)).inv ≫
    Functor.whiskerRight (theta D W₀ A m hm).hom (B D W₀ A 1) ≫
    (Functor.associator (L D W₀ A) (B D W₀ A m) (B D W₀ A 1)).hom ≫
    Functor.whiskerLeft (L D W₀ A) (d D W₀ A m).hom

/-- The left side u_(m+1)(t_m R) of the mate identity, before evaluation at K.
Source: Stacks 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def mateLeft (m : ℕ) :
    R D W₀ A ⋙ (Q D A m ⋙ Q D A 1) ⟶ B D W₀ A (m + 1) ⋙ R D W₀ A :=
  Functor.whiskerLeft (R D W₀ A) (t D A m).hom ≫
    exchange D W₀ A (m + 1) (Nat.succ_le_succ (Nat.zero_le m))

/-- The right side R(d_m)(u_1 B_m)Q_1(u_m), with explicit associators.
Source: Stacks 0E47 (blueprint: lem-trf-frobenius-proper-power-exchange). -/
def mateRight (m : ℕ) (hm : 1 ≤ m) :
    R D W₀ A ⋙ (Q D A m ⋙ Q D A 1) ⟶ B D W₀ A (m + 1) ⋙ R D W₀ A :=
  (Functor.associator (R D W₀ A) (Q D A m) (Q D A 1)).inv ≫
    Functor.whiskerRight (exchange D W₀ A m hm) (Q D A 1) ≫
    (Functor.associator (B D W₀ A m) (R D W₀ A) (Q D A 1)).hom ≫
    Functor.whiskerLeft (B D W₀ A m) (exchange D W₀ A 1 (Nat.le_refl 1)) ≫
    (Functor.associator (B D W₀ A m) (B D W₀ A 1) (R D W₀ A)).inv ≫
    Functor.whiskerRight (d D W₀ A m).hom (R D W₀ A)

/-- Canonical proper Frobenius power comparisons and their mates satisfy horizontal pasting.
Both equations are equalities of natural transformations on the entire ambient derived
categories; evaluation at K is the displayed component equation of the node.
Source: Stacks 0E47, remark-compose-base-change-horizontal, and 0D6D;
Deligne, Weil II (1.1.10)--(1.1.11)
(blueprint: lem-trf-frobenius-proper-power-exchange).
Proof:
1. The geometry theorem proves the canonical power lift is Cartesian with scheme
   isomorphisms on the horizontal sides, using lem-weil-frobenius-square-cartesian
   and the fibre-product inverse b^(-r) pi_W.
2. The coefficient absolute-value and DVR lemmas and lem-weil-valued-dvr-finite-quotients
   make A = O_E/(varpi_E^n) finite. lem-trf-constant-coefficient-composition fixes
   all constant-ring identifications, including the composite ones.
3. Apply lem-pur-factorized-pullback-square-pasting with u=p, r=(b,h), s=(b^m,h^m).
   The inverse compositors in that theorem are t_m and d_m. Transport along the
   power equalities, then cancel their inverse pairs, to obtain the first equation.
4. Apply lem-weil-pbc-mate-pasting with alpha=theta_m and beta=theta_1, using the
   same canonical adjunction L ⊣ R at all three vertical sides. The mate of
   (B_1 theta_m)(theta_1 Q_m) is (u_1 B_m) Q_1(u_m).
5. Apply lem-weil-pbc-mate-whisker to the equality in step 3, first at the top
   boundary t_m, then at the bottom boundary d_m. Substitute step 4. This yields
   the second equality as natural transformations, hence at every K and naturally
   in every derived morphism. No boundedness, constructibility or k-linearity is used. -/
theorem pasting (D : FiniteFieldDatum.{u})
    (W₀ : Over (Spec (.of D.k₀))) [IsProper W₀.hom]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (_hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    squareLeft D W₀ (Padic.coefficientExtensionRing l E n) m =
      squareRight D W₀ (Padic.coefficientExtensionRing l E n) m hm ∧
    mateLeft D W₀ (Padic.coefficientExtensionRing l E n) m =
      mateRight D W₀ (Padic.coefficientExtensionRing l E n) m hm := by
  sorry

end WeilConjectures.FrobeniusProperPower
