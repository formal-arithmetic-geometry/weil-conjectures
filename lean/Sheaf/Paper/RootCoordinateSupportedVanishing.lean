/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Localization.Away.Basic

import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity
import Sheaf.AlgebraicGeometry.SNCFiniteRootRegularRing
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# One-coordinate supported vanishing on the full tame root tower

Source: blueprint main-20261015, direct-images proof paragraph (3), agent-formulated
one-coordinate support input and its six-step DAG proof. This is not asserted to be
a quoted theorem of the blueprint. The norm-algebraic-closure coefficient input remains
an explicit analytical obligation in that proof.
(blueprint: lem-sfb-root-coordinate-supported-vanishing).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The ring of T_J, obtained by inverting the selected product in the full root algebra.
Source: the displayed T_J in the one-coordinate support input, direct-images paragraph (3)
(blueprint: lem-sfb-root-coordinate-supported-vanishing). -/
abbrev coordinateSupportRing (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (J : Finset (Fin r)) :=
  Localization.Away (algebraMap R (tameRootAlgebra p t) (∏ b ∈ J, t b))

/-- The original coordinate t_a as a global section on T_J. It is not a chosen root.
Source: the equation defining D_{a,J}, direct-images paragraph (3)
(blueprint: lem-sfb-root-coordinate-supported-vanishing). -/
def coordinateSupportSection (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (J : Finset (Fin r)) (a : Fin r) :
    Γ(Spec (.of (coordinateSupportRing p t J)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (coordinateSupportRing p t J))).inv
    (algebraMap (tameRootAlgebra p t) (coordinateSupportRing p t J)
      (algebraMap R (tameRootAlgebra p t) (t a)))

/-- The scheme-theoretic coordinate divisor, cut out by t_a itself on T_J.
Source: the closed inclusion d_{a,J}, direct-images paragraph (3)
(blueprint: lem-sfb-root-coordinate-supported-vanishing). -/
def coordinateSupportIdeal (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (J : Finset (Fin r)) (a : Fin r) :
    (Spec (.of (coordinateSupportRing p t J))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {coordinateSupportSection p t J a})

/-- The principal open complement of D_{a,J}; this is T_{J union {a}} over T_J.
Source: the complementary open in the one-coordinate support input, paragraph (3)
(blueprint: lem-sfb-root-coordinate-supported-vanishing). -/
def coordinateSupportComplement (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (J : Finset (Fin r)) (a : Fin r) :
    (Spec (.of (coordinateSupportRing p t J))).Opens :=
  (Spec (.of (coordinateSupportRing p t J))).basicOpen (coordinateSupportSection p t J a)

/-- The one-coordinate supported object is zero for each supplied lisse module on T.
The module is restricted along the canonical localization morphism T_J -> T, placed
in degree zero, and then the full closed-support functor is right-derived.
Source: the displayed supported-vanishing formula, direct-images paragraph (3)
(blueprint: lem-sfb-root-coordinate-supported-vanishing). -/
def RootCoordinateSupportedVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) : Prop :=
  ∀ (N : CondensedRing.supportModules Λ (Spec (.of (tameRootAlgebra p t)))),
    IsLisseCoefficientModule Λ N →
    ∀ (J : Finset (Fin r)) (a : Fin r), a ∉ J →
      IsZero
        ((CondensedRing.closedSupport Λ (coordinateSupportIdeal p t J a).subschemeι
          (coordinateSupportComplement p t J a).ι).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.upperStar Λ
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (tameRootAlgebra p t) (coordinateSupportRing p t J))))).obj N)))

/-- Vanishing with support in one un-inverted boundary coordinate on the full tame root
tower, for the actual all-continuous E and normed algebraic closure coefficients.
Source: agent-formulated input in direct-images paragraph (3), blueprint main-20261015
(blueprint: lem-sfb-root-coordinate-supported-vanishing).

Proof: (1) Form the finite root algebras B_n and localize at the J-coordinate product.
Monic division makes their transitions finite free. The SNC root regularity lemma and
its face version show that each stage and its coordinate divisor are regular; freeness
preserves the nonzerodivisor condition. (2) Finite supported Cartier purity over Z/ell^s
concentrates the support fibre in degree two. Its transition from n to m is m/n times
the Tate-line exchange, hence is zero at m = n ell^s, an allowed prime-to-p index.
(3) Stacks 0EYM computes higher open direct images at the inverse limit by the same
exchange transitions. Exact filtered colimits kill every cohomology sheaf of the fibre,
so the actual finite-coefficient open unit is invertible. (4) The etale/pro-etale
comparison for the qcqs principal open preserves that unit. (5) Apply the separate
norm-coefficient criterion to this system and its affine pro-etale base change U -> V.
Root colimits and localization commute with that base change, giving exactly T_J and
its principal puncture. The supplied lisse module restricts to a lisse module, so the
criterion makes its actual open unit invertible, separately for E and Omega. This is
the unsplit analytical input for the possibly incomplete normed Omega, not a claim
of completeness or of finite-subextension descent. (6) The formal closed-support
fibre formula identifies the derived supported object with exact closed pullback of
the fibre of that unit; it is zero. Empty divisors give the identity open, rank zero
gives zero objects, and r = 0 gives no allowed coordinate. -/
theorem rootCoordinate_supported_vanishing
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R] (a : A →+* R)
    [WeaklyEtale (Spec.map (CommRingCat.ofHom a))] :
    RootCoordinateSupportedVanishing (Profinite.continuousCoefficientRingObj E)
      p (fun i ↦ a (t i)) ∧
    RootCoordinateSupportedVanishing (Profinite.continuousCoefficientRingObj Ω)
      p (fun i ↦ a (t i)) := by
  sorry

end AlgebraicGeometry.ProEtale
