/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingComposition
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition

/-!
# Coherence of Frobenius-power pullback comparisons

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, the m-th-iterate assertion;
Stacks Project, Tag 0D6D
(blueprint: lem-trf-frobenius-pullback-comparison-coherence).

Positive exponents are indexed by their predecessor: index `r` means exponent `r + 1`.
The two binary-splitting equations encode every ordered splitting tree, and hence every
finite positive partition and reassociation. Both orders of refining the two branches
are displayed. All helpers construct the comparisons explicitly, without choosing maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

namespace TraceFormulaCoefficientConventions

/-- The actual ordinary pullback `P_(r+1) = L(g^(r+1))^*`, for geometric Galois Frobenius.
This is the recorded `geometricGaloisDerivedPullback` of def-trf-scheme-frobenius at
exponent `r + 1`, i.e. `proEtaleConstantRingDerivedPullback` along `g^(r+1)`.
Source: blueprint, m-th-iterate assertion
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
abbrev frobeniusPullbackPower (S : TraceFormulaCoefficientConventions.{u}) (r : ℕ) :=
  S.datum.geometricGaloisDerivedPullback S.X₀ S.coefficientRing (r + 1)

end TraceFormulaCoefficientConventions
end WeilConjectures
