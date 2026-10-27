/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.BoundaryQTransport
import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.DualityPairing
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-! # Boundary q and evaluation under site comparison

Source: blueprint boundary-duality discharge, final paragraph
(blueprint: lem-weil-boundary-proetale-q-compatibility).
The finite-level coefficients, sites, constructibility and Tor predicates, exceptional
functors, canonical projection maps and comparison arrows are the recorded ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
open BoundaryComparison

/-- Specialization to the actual positive finite coefficient level and the dualizing
objects of the two structure morphisms. All let instances are derived from the stated
geometry or the recorded finiteness theorem; they add no hypotheses.
Source: blueprint boundary-duality discharge, finite-level setting
(blueprint: lem-weil-boundary-proetale-q-compatibility). -/
def BoundaryQFiniteConclusion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))
  BoundaryQCompatibility (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i
    (WeilConjectures.finiteTorConstructibleEtale l E n hn T) ∧
  BoundaryDualityCompatibility (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i
    (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
    (WeilConjectures.finiteTorConstructibleEtale l E n hn Z)
    (finiteDualityEtaleObject (Padic.coefficientExtensionRing l E n)
      (NagataCompactification (T ↘ Spec (.of D.k))))
    (finiteDualityEtaleObject (Padic.coefficientExtensionRing l E n)
      (NagataCompactification (Z ↘ Spec (.of D.k))))

/-- Comparison transports q and the evaluation-defined tensor-Hom transposes, including
the displayed boundary pairing. The conclusion unfolds to the actual sites and finite
coefficient categories; q uses the ordinary counit-defined projection inverses.
Source: blueprint boundary-duality discharge, final paragraph
(blueprint: lem-weil-boundary-proetale-q-compatibility).

Proof:
1. Put B = G_e N. Use the assumed ProjectionComparison for the recorded counit-defined
   projection components (def-kun-projection-formula-map). Invert its square, since the
   two displayed projection components are isomorphisms. On K-flat representatives,
   the monoidal comparison commutes with Koszul symmetry. Naturality moves eta past
   the first symmetry, the inverse projection square moves it past pi inverse, and
   CounitComparison replaces the resulting counit composite. This identifies C_T(t_e)
   after eta with t_p after F_p of the source comparison, including 1 tensor theta_N
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-comparison-pullback).
2. Transpose the equality from step 1 through the recorded exceptional Hom transport.
   The comparison theta is the mate of eta, as its unit and counit normalizations show.
   Naturality of this Hom bijection therefore gives C_Z(q_e) followed by theta at
   M tensor N equal to the pro-etale q in comparison coordinates. This is exactly
   BoundaryQCompatibility; no ambient pro-etale exceptional adjoint is asserted.
3. The evaluation-defined Hom comparison identifies evaluation and its transpose by
   lem-weil-finite-duality-site-comparison and lem-weil-duality-pairing. Transposing its
   defining evaluation square gives PairingTransposeEquality for every pairing. Step 2
   supplies the q square, and step 1 the symmetry square. Naturality and cancellation
   compose these squares through each finite composite, so the same transport applies
   to every pairing made from q, evaluation and symmetry, including double-dual maps.
4. For the displayed pairing take N representing D_T K. Apply step 2 to its q factor,
   step 3 to evaluation using chi_T, and the assumed compatible dualizing square to
   G(omega_T) -> omega_Z. The explicit formulas etaleBoundaryPairing and
   proBoundaryPairingCoordinates then have equal transported transposes under chi_Z.
   The stipulated finite-Tor conditions on K, its dual, their inverse and exceptional
   images, and their duals place all these arrows in the stated comparison class.
-/
theorem boundary_proetale_q_compatibility
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i] :
    BoundaryQFiniteConclusion D l hl E n hn i := by
  sorry

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
