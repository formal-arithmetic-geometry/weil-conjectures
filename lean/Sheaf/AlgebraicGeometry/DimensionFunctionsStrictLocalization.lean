/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.GeometricDimensionFunction
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Dimension functions and strict localization

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Definition 2.1.8
and the following paragraph, pp. 211--212; the strict-local reduction in the proof of
Proposition 2.5.4, p. 217 (blueprint: lem-per-dimension-functions-strict-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A function on a Noetherian excellent scheme is a dimension function exactly when
its pullback to every strict localization is a dimension function. In particular the
forward implication gives restriction to each individual strict localization.
Source: ILO XIV, Definition 2.1.8 and following paragraph, pp. 211--212; Proposition
2.5.4, p. 217 (blueprint: lem-per-dimension-functions-strict-localization).

Proof:
1. Fix a geometric point barT and put L = T_(barT), with structural map pi. An affine
   open U of T containing its image contains the image of all of L: an open in a local
   spectrum containing the closed point is the entire spectrum. By
   lem-weil-pbc-strict-henselization-affine-chart-ind-etale, pi is locally ind-etale.
   Clause (1) of lem-weil-pbc-strict-henselization-functoriality supplies its closed
   geometric lift c with pi composed with c equal to barT.
2. Suppose d is a dimension function on T. For an immediate geometric specialization
   on L with special endpoint b, lem-trf-ind-etale-strict-local-invariance identifies
   L_(b) with T_(pi b) over T. The isomorphism identifies the reduced closures of the
   general points and preserves their dimension one. Functoriality clause (1) identifies
   the images of the closed points. The defining equation on T is therefore exactly
   the defining equation for d composed with pi on L.
3. Conversely, take an immediate geometric specialization on T with special endpoint
   barT and general point v in L. By the closed-point iteration clause of
   lem-trf-ind-etale-strict-local-invariance, the canonical map phi : L_(c) -> L is an
   isomorphism over T, so pi composed with phi equals pi composed with the structural
   map j : L_(c) -> L. Its inverse carries v to v', with one-dimensional reduced
   closure. Apply the assumed dimension-function equation on L to v' and c. Clause
   (1) of functoriality identifies the special image with t, and pi(j(v')) = pi(v).
   This is exactly the required equation on T. The final pullback assertion is the
   forward implication, specialized to the chosen geometric point.
-/
theorem isGeometricDimensionFunction_iff_strictLocalization
    (T : Scheme.{u}) [IsNoetherian T]
    (hT : ∀ U : T.affineOpens, IsExcellent Γ(T, U)) (d : T → ℤ) :
    IsGeometricDimensionFunction T d ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (barT : Spec (.of Ω) ⟶ T),
        IsGeometricDimensionFunction (strictHenselizationScheme barT)
          (fun x ↦ d (strictHenselizationStructuralMap barT x)) := by
  sorry

end AlgebraicGeometry.Scheme
