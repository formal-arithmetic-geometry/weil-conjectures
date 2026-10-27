/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison

/-!
# Étale restriction of a log regular structure

Source: ILO VI 1.1--1.2 (blueprint: lem-trf-etale-log-regular-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Log regularity and the triviality locus pull back under an étale slice restriction.
Source: ILO VI 1.1--1.2, printed p. 69; step 1 of
lem-trf-free-log-chart-ordinary-parameters.
(blueprint: lem-trf-etale-log-regular-restriction).

Proof: the pointed neighbourhood category over W is the slice of that over X at
its pointed étale object W. The forgetful functor is initial, so restriction induces
isomorphisms on monoid and ring stalks, commuting with the structural map and units.
An fs chart near the image of a geometric point restricts after fibre product with W;
the same pushout and stalk isomorphisms prove its chart condition. This proves fs.
The monoid isomorphism induces the characteristic isomorphism and preserves its
rational group-completion rank. The compatible ring isomorphism carries the generated
nonunit ideal to the nonunit ideal; hence it identifies the stratum quotients and
preserves their regularity and both Krull dimensions. Apply log regularity on X.
For the locus assertion, the same isomorphism preserves subsingleton characteristics.
Every geometric point of W maps to one of X. Conversely, the residue extension
at a point of an étale morphism is finite separable, so any embedding of the base
residue field into an algebraically closed field extends to the source residue field.
Thus any geometric point at its image lifts through the prescribed source point.
The same stalk identification makes the universal geometric-point conditions in
the two triviality loci equivalent. This includes the empty scheme. -/
theorem etale_logRegular_restriction
    (X : FineSaturatedLogScheme.{u}) (hX : X.IsLogRegular)
    (W : X.scheme.Etale) [IsLocallyNoetherian W.left]
    (N : EtaleLogStructure W.left)
    (hN : N.toEtalePrelogStructure = X.logStructure.toEtalePrelogStructure.etaleRestrict W) :
    (∃ hfs : N.IsFineSaturated,
      FineSaturatedLogScheme.IsLogRegular ⟨W.left, inferInstance, N, hfs⟩) ∧
      W.hom ⁻¹' X.logStructure.trivialityLocus = N.trivialityLocus := by sorry

end AlgebraicGeometry
