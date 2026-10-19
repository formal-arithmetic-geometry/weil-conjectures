/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes

/-!
# Finite-stage direct image with the dimension Tor bound

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-thm-sf-direct-image-tor-amplitude/_section.md`, order 1712
(blueprint: sk-thm-sf-direct-image-tor-amplitude).

Both constructibility clauses use the predicate recorded by
`def-weil-pbc-constructible-complexes`, and the Tor predicates test every degree-zero
module sheaf. All functors are on ordinary small etale module-sheaf derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Finite-stage direct image preserves bounded constructibility and carries the Tor
interval `[a,b]` into `[a,b+2d]` over the standing algebraic closure of a finite field.
Source: main-20261015 blueprint, sec-six-functors-basics, order 1712, statement and proof
of `sk-thm-sf-direct-image-tor-amplitude`
(blueprint: sk-thm-sf-direct-image-tor-amplitude).

Proof plan:
1. The coefficient definition, lem-weil-l-adic-extension-integers-dvr and
lem-weil-valued-dvr-finite-quotients give a finite local Noetherian ring A, with residue
field kappa. The extended absolute value gives l in the uniformizer ideal, hence l^n A = 0;
l^n is invertible in the standing field because l differs from its characteristic.
2. Put L = K tensor^L kappa_X. Test def-kun-tor-amplitude against kappa_X to obtain
cohomology only in [a,b]. A good lower truncation at a has zero terms below a, the
cokernel of the preceding differential in degree a, and the original terms above a.
The projection to this complex is a quasi-isomorphism, giving a bounded-below representative.
3. Module sheaves are Grothendieck abelian by
lem-weil-pbc-module-sheaves-grothendieck-abelian and direct image is additive and left exact
by lem-weil-pbc-module-direct-image-left-exact. Apply thm-sp-truncation-e2 to this
representative: E2^{p,q} = R^p f_* H^q(L) abuts to H^{p+q}(Rf_*L).
4. The all-module-sheaf bound lem-sf-etale-direct-image-vanishing gives
HasUniformDirectImageVanishingLE A f (2*d), as in def-sf-uniform-direct-image-vanishing.
The page is supported in 0 <= p <= 2d and a <= q <= b. Outside total degrees [a,b+2d]
the stable terms vanish. The finite exhaustive separated abutment filtration from
thm-sp-truncation-e2 then gives zero cohomology in those degrees.
5. Apply thm-dg-finite-type-constructibility: A is finite, its exponent is invertible
in the field, both schemes are finite type, and K is bounded constructible. Thus
F = Rf_*K is bounded constructible.
6. The presentation A --uniformizer--> A --> kappa --> 0 makes kappa finitely presented.
Apply lem-sf-projection-finite-constant, using Noetherian A, the uniform bound and
boundedness above of K. Its canonical map of def-kun-projection-formula-map identifies
F tensor^L kappa_Y with Rf_*L. Both the unbounded direct image and the bounded-below
one of def-weil-pbc-direct-image are computed by Q(f_*I) for K-injective resolutions,
so they agree on K and L. Step 4 therefore gives the required residue-tensor vanishing.
7. Apply lem-exc-residue-tor-test to the bounded constructible F with endpoints a and
b+2d. It gives the asserted Tor amplitude; Step 5 supplies the other conclusion. -/
theorem finiteStage_directImage_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (_hK : @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      _ (Padic.finite_coefficientExtensionRing l E n hn) X K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) X a b K) :
    @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
        _ (Padic.finite_coefficientExtensionRing l E n hn) Y
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a
        (b + 2 * (d : ℤ))
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) := by
  sorry

end AlgebraicGeometry.Etale
