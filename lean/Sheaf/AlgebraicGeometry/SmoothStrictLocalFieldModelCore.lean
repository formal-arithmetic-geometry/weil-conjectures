/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.Unramified.LocalRing
import Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence
import Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.RingTheory.StrictHenselizationRegular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.RingTheory.StrictHenselizationDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.RingTheory.IndPrincipalZariski

/-! # The geometric core of a smooth strict localization

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 06LN, 06LK and 04GG.
(blueprint: lem-sc-smooth-strict-local-field-model-core)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Regularity, dimension, residue and function field of a smooth strict localization.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04HX, 04GW, 04GP, 00TT, 06LN, 00NP, 0A21 and 06LK.
(blueprint: lem-sc-smooth-strict-local-field-model-core)

Proof: choose a smooth affine chart U = Spec A at y and let p be its prime at y.
The stalk is B = A_p, and A is a domain since Y is integral. Restrict the affine
pointed-etale neighbourhoods to those lying over U: every neighbourhood has such
an affine refinement, so this restriction is cofinal. Their residue fields are
finite separable over kappa(y); hence the specified maps into Omega land in
l = separableClosure (Y.residueField y) Omega. The chart/residue-triples comparison
identifies the coordinate-ring colimit R with the triples colimit. The localized
triples theorem equips this same ring with its B-algebra strict henselization
structure, preserving its structural map. The triples theorem gives a surjection
rho : R -> l with maximal-ideal kernel. It induces the asserted residue-field
isomorphism e. Its equations on every colimit leg, followed by l -> Omega, give
Spec(rho) followed by the structural map equal to s, exactly the displayed
compatibility; hOmega and hy identify the prescribed residue-field embedding.

Smoothness makes B regular local and Noetherian. Strict henselization preserves
regularity, and a regular local ring is a domain. The map B -> R is faithfully
flat, hence injective. Thus A -> B -> R -> Q = Frac(R) embeds Frac(A) in Q.
Identify Frac(A) with Y.functionField using the generic stalk of the integral
scheme. On the affine chart both structural composites are induced by the same
A-map; the localization universal property and the open immersion give the
stated equality of morphisms from Spec Q to Y.

Every nonempty open of the integral locally algebraic Y has dimension d, so
its dimension at y is d. The finite-type point dimension formula gives
 dim B + trdeg_K kappa(y) = d. With ha this implies a <= d and dim B = d-a.
Strict henselization preserves this local dimension, proving the dimension of R.
The algebra structures used in this calculation agree with the given ones:
hK and hKappa (hκ in Lean), together with the structural-map equations, fix them
by full faithfulness of Spec and the monomorphism Spec(kappa(y)) -> Y.

Finally the affine-chart ind-etale theorem writes R as a filtered colimit of
etale A-algebras C. Represent the numerator r and nonzero denominator t of any
r/t in Q at one common stage C. The kernel q of C -> R -> Q contracts to zero
in A, since A -> Q is injective. Therefore C/q embeds in Q, and its fraction
field kappa(q) is finite separable over kappa(0) = Frac(A), by etaleness.
The representative of t has nonzero image, so r/t belongs to this embedded
field. Consequently every element of Q is algebraic over Y.functionField,
with the algebra structure specified by the structural embedding i. -/
theorem smooth_strict_local_field_model_core
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f) :
    IsRegularLocalRing (strictHenselizationRing s) ∧
    ∃ hlocal : IsLocalRing (strictHenselizationRing s),
      ∃ hdomain : IsDomain (strictHenselizationRing s),
        letI := hlocal
        letI := hdomain
        ringKrullDim (strictHenselizationRing s) = ((d - a : ℕ) : WithBot ℕ∞) ∧
        ∃ e : IsLocalRing.ResidueField (strictHenselizationRing s) ≃+*
            separableClosure (Y.residueField y) Ω,
          Spec.map (CommRingCat.ofHom
            ((separableClosure (Y.residueField y) Ω).subtype.comp
              (e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing s))))) ≫
            strictHenselizationStructuralMap s = s ∧
          ∃ i : Y.functionField →+* FractionRing (strictHenselizationRing s),
            Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
              Spec.map (CommRingCat.ofHom
                (algebraMap (strictHenselizationRing s)
                  (FractionRing (strictHenselizationRing s)))) ≫
                strictHenselizationStructuralMap s ∧
            (letI := i.toAlgebra
             Algebra.IsAlgebraic Y.functionField (FractionRing (strictHenselizationRing s))) := by
  sorry

end Scheme
end AlgebraicGeometry
