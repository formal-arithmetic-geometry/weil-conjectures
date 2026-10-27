/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupUniversalProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Normalized blowup finality over a locally Noetherian base

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII 2.2.1--2.2.4(i),
printed p.90; Stacks Project, Tags 0808, 0BFM, 0806 and 035Q
(blueprint: lem-per-noetherian-normalized-blowup-finality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Over a reduced locally Noetherian base, the ordinary blowup is reduced, locally
Noetherian, proper, surjective and generically an isomorphism on points and residue fields.
Its componentwise normalization is normal and has the same generic and surjectivity
properties. The extended centre is an effective Cartier ideal, and the normalized blowup
is final for component-generically dominating maps from arbitrary normal schemes on which
that ideal is effective Cartier. No local Noetherianity is required of the normalization
or of the test scheme.

Source: ILO, VIII 2.2.1--2.2.4(i), printed p.90; Stacks Tags 0808, 0BFM, 0806 and 035Q
(blueprint: lem-per-noetherian-normalized-blowup-finality).

Proof:
1. The scheme case of lem-sfb-space-blowup-chart-properties gives properness, the
isomorphism over U = S minus V(J), and charts R[J/a] where the extended ideal is (a).
These charts are subrings of R localized at a, so a is a nonzerodivisor. On a Noetherian
reduced affine cover of S, pqf-lem-coherent-ft-locnoeth supplies coherence and
lem-per-reduced-noetherian-blowup-geometry gives reduced Noetherian inverse images.
These cover the blowup W, proving reducedness and local Noetherianity.
2. By lem-weil-pbc-reduced-zerodivisors-union-minimal-primes no component generic point
of W lies in the exceptional Cartier divisor. Generic points correspond to minimal primes
by lem-weil-pbc-spec-irreducible-components-minimal-primes and are unique by
lem-weil-pbc-scheme-sober. The open-component correspondence follows from
lem-sc-components-open-injection and lem-sc-irreducible-components-cover. The isomorphism
above U therefore bijects generic points and identifies their residue fields. Properness
makes the image closed; it contains dense U and hence all of S.
3. Apply lem-per-componentwise-normalization-properties(1) to W: its normalization N
is normal and surjective with the same generic points and generic residue fields. Compose
with the preceding bijections. A quasi-compact open of W is Noetherian and has finitely
many components by lem-weil-pbc-noetherian-finitely-many-components; no such assumption
is needed on N.
4. On an affine Cartier-generator chart Spec A of W, use
lem-sfb-normalization-affine-total-fractions to identify the normalized chart with the
integral closure of A in Q(A). The regular generator a is a unit in Q(A), so it remains
a nonzerodivisor on this subring. Extension of ideals composes, proving that J O_N is
invertible without any flatness assumption on normalization.
5. For a test map g, lem-sfb-space-blowup-universal-property gives a unique lift to W.
The Zariski regular generators remain regular on etale charts by flatness. For
representable spaces Yoneda identifies this lift with an actual scheme map. A component
generic point of Z maps to a generic point in U; the isomorphism above U takes its lift
to the corresponding generic point of W. Continuity shows that its whole component
dominates that component of W.
6. Apply lem-sfb-component-dominant-normalization-lift, using the finite-component
condition on quasi-compact opens verified in step 3. This gives the lift Z to N. Any two
S-maps have the same composite to W by blowup uniqueness, and normalization uniqueness
then identifies them. Both mapping properties permit empty schemes and arbitrary normal
Z. The unit ideal recovers normalization finality, and no characteristic, excellence or
finiteness of normalization has been used. -/
theorem noetherian_normalizedBlowup_finality (S : Scheme.{u})
    [IsReduced S] [IsLocallyNoetherian S] (J : S.IdealSheafData)
    (hJ : ∀ U : S.affineOpens, (J.ideal U).FG)
    (hcentre : Dense (J.support.compl : Set S)) :
    IsReduced J.blowup ∧ IsLocallyNoetherian J.blowup ∧
    IsProper J.blowupMap ∧ Surjective J.blowupMap ∧
    Set.BijOn J.blowupMap
      {x : J.blowup | ∃ C ∈ irreducibleComponents J.blowup, IsGenericPoint x C}
      {x : S | ∃ C ∈ irreducibleComponents S, IsGenericPoint x C} ∧
    (∀ x : J.blowup, (∃ C ∈ irreducibleComponents J.blowup, IsGenericPoint x C) →
      IsIso (J.blowupMap.residueFieldMap x)) ∧
    (∀ x : J.blowup.reducedNormalization,
      IsDomain (J.blowup.reducedNormalization.presheaf.stalk x) ∧
      IsIntegrallyClosed (J.blowup.reducedNormalization.presheaf.stalk x)) ∧
    Surjective (J.blowup.fromReducedNormalization ≫ J.blowupMap) ∧
    Set.BijOn (J.blowup.fromReducedNormalization ≫ J.blowupMap)
      {x : J.blowup.reducedNormalization |
        ∃ C ∈ irreducibleComponents J.blowup.reducedNormalization, IsGenericPoint x C}
      {x : S | ∃ C ∈ irreducibleComponents S, IsGenericPoint x C} ∧
    (∀ x : J.blowup.reducedNormalization,
      (∃ C ∈ irreducibleComponents J.blowup.reducedNormalization, IsGenericPoint x C) →
      IsIso ((J.blowup.fromReducedNormalization ≫ J.blowupMap).residueFieldMap x)) ∧
    (J.comap (J.blowup.fromReducedNormalization ≫ J.blowupMap)).IsInvertible ∧
    (∀ (Z : Scheme.{u}) (g : Z ⟶ S),
      (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
        IsIntegrallyClosed (Z.presheaf.stalk z)) →
      Set.MapsTo g
        {z : Z | ∃ C ∈ irreducibleComponents Z, IsGenericPoint z C}
        {x : S | ∃ C ∈ irreducibleComponents S, IsGenericPoint x C} →
      (J.comap g).IsInvertible →
      ∃! h : Z ⟶ J.blowup.reducedNormalization,
        h ≫ J.blowup.fromReducedNormalization ≫ J.blowupMap = g) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
