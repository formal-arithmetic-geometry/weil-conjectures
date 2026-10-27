/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.TraceFormula.CompactFrobeniusTransportComposition
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.FrobeniusPullbackComparisonCoherence
public import Sheaf.Paper.TraceFormulaLocalFrobeniusOperator
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.CategoryTheory.NaturalTransportInduction
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-!
# Direct compact-support transport agrees with repeated transport

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, second sentence;
expanded DAG proof, steps 1--4
(blueprint: lem-trf-compact-direct-power-transport-normalization).

The index `r` represents the positive exponent `r + 1`. The same compactification
is retained for every power. The direct transport is the published direct exchange,
expressed in the canonical tensor-pullback coordinates of the published comparison d.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The specified direct power transport, in the coordinates of the actual d comparison.
The map is `compactPowerTransport` followed only by H of the unit-normalized
`pointPowerPullbackModel`; it is not defined by iterating degree-one transport.
Source: main-20261015 blueprint, compact-description proof, second sentence;
DAG lem-trf-compact-frobenius-transport-composition, direct transport recipe
(blueprint: lem-trf-compact-direct-power-transport-normalization). -/
def compactDirectPowerTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    exact compactPowerTransport D C.l C.different F X c₀ n (r + 1) M ≫
      (finiteGlobalCompactSections ⟨D, C, E, n + 1, hn, X⟩ c₀).map
        ((pointPowerPullbackModel C.l F n
          ((End.of (D.geometricGaloisFrobenius X)) ^ (r + 1))).hom.app M)

/-- Direct power transport equals exactly r+1 degree-one transports followed by H(d⁻¹).
Both pullback presentations remain bounded constructible, and both displayed maps are
isomorphisms of derived coefficient complexes. No Weil structure or finite Tor amplitude
is required.
Source: main-20261015 blueprint, compact-description proof, second sentence;
expanded DAG proof of lem-trf-compact-direct-power-transport-normalization, steps 1--4
(blueprint: lem-trf-compact-direct-power-transport-normalization).

Proof:
1. Lem-weil-frobenius-square-cartesian identifies g and hence every power as an
   isomorphism. The finite-coefficient clause of lem-weil-isomorphism-derived-pullback
   preserves bounded constructibility under each power, and repeatedly under T = P_1.
   The canonical presentation comparison transports this conclusion to the actual P_r.
2. Retain c₀. Lem-trf-compact-frobenius-transport-composition gives the direct transport
   recurrence with the inverse canonical pullback compositor. Naturality of degree-one
   transport is def-weil-frobenius-cohomology-transport. The actual d_r are those of
   def-trf-frobenius-pullback-power-comparison; their normalization and successor equation
   are lem-trf-frobenius-pullback-comparison-coherence. The unit-normalized presentation
   comparisons identify these with the same compositor in intrinsic coordinates.
3. Apply lem-trf-frobenius-transport-induction to H, T, these actual comparisons and the
   specified direct transports. Its identity base case and successor calculation give
   precisely the displayed equality in the derived category before taking cohomology.
4. Lem-weil-frobenius-cohomology-transport-iso, finite clause 3, makes every degree-one
   factor invertible at the bounded constructible iterates from step 1. H(d_r⁻¹) is
   invertible by functoriality. Their composite is invertible, and step 3 gives the same
   assertion for direct transport. No Weil map or finite Tor-amplitude enters. -/
theorem compact_direct_power_transport_normalization
    (T : TraceFormulaCoefficientConventions.{u}) (c₀ : Compactification T.X₀.hom)
    (M : T.boundedConstructible.FullSubcategory) (r : ℕ) :
    T.boundedConstructible ((T.frobeniusPullbackPower r).obj M.obj) ∧
    T.boundedConstructible
      ((trfPositiveFunctorPower (T.frobeniusPullbackPower 0) r).obj M.obj) ∧
    T.finiteGlobalComparedTransport c₀ M.obj r = T.compactDirectPowerTransport c₀ M.obj r ∧
    IsIso (T.finiteGlobalComparedTransport c₀ M.obj r) ∧
    IsIso (T.compactDirectPowerTransport c₀ M.obj r) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
