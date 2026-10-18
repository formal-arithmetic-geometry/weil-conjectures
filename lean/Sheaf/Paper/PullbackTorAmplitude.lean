/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Pullback preserves finite Tor amplitude

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2064 (blueprint: lem-sf-pullback-tor-amplitude).
The finite pullback below specializes the recorded ringed-site operation along the
canonical constant-section coefficient isomorphism. It introduces no chosen ring map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite-level derived pullback on the recorded constant-ring module category.
The coefficient comparison is the canonical inverse-image map, whose invertibility
is the recorded constant-coefficient theorem. Exact module pullback descends termwise.
Source: blueprint order 2064, finite-level operation from order 1467;
Stacks Tags 03D2 and 0735 (blueprint: lem-sf-pullback-tor-amplitude). -/
noncomputable def sfFiniteDerivedPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  letI := ProEtale.finiteCoefficientCommRingMap_isIso f
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
  proEtaleRingDerivedPullback f
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))
    (asIso (proEtaleCoefficientInverseImageMap f (Padic.coefficientExtensionRing l E n)))

/-- Pullback preserves bounded constructibility and the very same Tor interval.
Source: Weil blueprint, order 2064 (blueprint: lem-sf-pullback-tor-amplitude).
Proof:
1. Specialize the complete coefficient datum to O_E and its uniformizer ideal.
The finite residue field makes every quotient finite; the DVR is Noetherian.
By lem-weil-pbc-standard-quotients-perfect the quotients are perfect, and the
valuation identity l = unit times uniformizer^e makes them l-power torsion.
Since l differs from p, their orders are invertible on these k-schemes.
Use lem-sf-proetale-constructible-origin on both schemes to identify intrinsic
constructibility with etale origin. Then
lem-weil-pbc-pullback-preserves-bounded-constructible gives bounded constructibility.
2. By lem-sf-flat-model choose an isomorphism K ≅ Q(P), with P flat termwise
and zero outside [a,b]. No chain map from P to an arbitrarily chosen K is needed.
3. P is bounded above and flat, so lem-pc-bounded-above-flat-kflat-site makes
it K-flat. Apply lem-weil-pbc-ringed-pullback-preserves-kflat to obtain a K-flat
pullback with flat terms. The canonical constant-ring comparison identifies its
terms with inverse image of P, hence they vanish outside the same interval.
Exact termwise inverse image computes derived pullback on every representative.
4. For every module sheaf N in degree zero, def-weil-derived-tensor computes
the derived tensor on this K-flat model. Its terms outside [a,b] vanish, hence
so do its cohomology sheaves. By def-weil-finite-tor-amplitude this is exactly
the asserted Tor interval. -/
theorem sf_pullback_torAmplitude
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn Y.left K)
    (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E n) K a b) :
    intrinsicFiniteTorsionConstructible l E n hn X.left
        ((sfFiniteDerivedPullback l E n hn f.left).obj K) ∧
      HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E n)
        ((sfFiniteDerivedPullback l E n hn f.left).obj K) a b := by
  sorry

/-- Consequently pullback carries Dᵇ_ctf(Y,A) into Dᵇ_ctf(X,A), clause (i) of the
finite-stage preservation summary. This is object-property preservation, so it
specifies the restriction of the same ambient functor to the full subcategories.
Source: Weil blueprint, order 2064 (blueprint: lem-sf-pullback-tor-amplitude).
Proof: unpack finiteTorConstructible to obtain bounded constructibility and one
ordered interval witnessing finite Tor amplitude. Apply sf_pullback_torAmplitude
with that interval. Its two conclusions, with the same interval as witness, are
the defining two conditions of finiteTorConstructible on X. -/
theorem sf_pullback_finiteTorConstructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E n))
    (hK : finiteTorConstructible l E n hn Y.left K) :
    finiteTorConstructible l E n hn X.left
      ((sfFiniteDerivedPullback l E n hn f.left).obj K) := by
  sorry

end WeilConjectures
