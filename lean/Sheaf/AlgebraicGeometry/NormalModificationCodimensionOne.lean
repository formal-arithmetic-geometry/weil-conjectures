/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization
import WeilConjectures.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# The isomorphism open of a proper birational modification

Source: Stacks Project, Varieties, Tag 0BFP, all four clauses
(blueprint: lem-sfb-normal-modification-codimension-one).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The maximal isomorphism open of a proper birational map with reduced source contains
all codimension-zero points, codimension-one DVR points, normal points with finite fibre,
and normal points with a quasi-finite point above them.

Source: Stacks Project, Varieties, Tag 0BFP
(blueprint: lem-sfb-normal-modification-codimension-one).

Birationality is stated using the component-generic points and the actual stalk maps.
`IsGreatest` says both that the restriction over `U` is an isomorphism and that every
other isomorphism open is contained in `U`. Normality of a local ring is equivalently
being an integrally closed domain. The domain binder in the DVR clause is part of the
DVR hypothesis, since Mathlib's DVR class takes the domain instance as a parameter.

Proof:
1. Properness gives separatedness and finite type [pqf-lem-proper-basic]. The source is
Noetherian [lem-weil-pbc-finite-type-over-noetherian], so both spaces have finitely many
components [lem-weil-pbc-noetherian-finitely-many-components]. Finite type over a locally
Noetherian scheme gives local finite presentation [pqf-lem-lft-fp-locnoeth]. Apply
[lem-sfb-birational-isomorphism-dense-open]. Its dense open contains every component generic
point: remove the finitely many other components and use density in the remaining open.
These are the codimension-zero points, proving (1).
2. Prove (4) first. At the given normal point, [lem-sfb-noetherian-injective-germ-neighbourhood]
gives an affine neighbourhood with its ring embedded in the normal local domain. This
neighbourhood is integral. Properness persists under restriction
[lem-weil-pbc-proper-base-change]. Birationality leaves exactly one source component, and
reducedness makes the restricted source integral [def-pc-integral-scheme].
3. Choose the affine witnesses for quasi-finiteness [pqf-def-quasifinite] inside these
neighbourhoods, using [lem-weil-pbc-quasi-finite-at-prime-principal-localization]. Apply
[lem-weil-pbc-quasi-finite-at-finite-subalgebra-away] to the resulting A-algebra C: obtain
finite B contained in C and g outside the chosen prime with B_g isomorphic to C_g.
[lem-sc-integral-function-field-affine-fraction] and birationality embed A, B and C into
their common fraction field K, compatibly with the germ maps.
4. By [lem-weil-pbc-affine-open-stalk-localization], the target stalk is R = A_p and the
source stalk is C_q. Localizing finite generators shows B_p is finite over R, hence integral
[lem-weil-pbc-finite-algebra-is-integral]. Normality [def-weil-pbc-normal-ring] forces
B_p = R inside K. The prime below q then becomes the maximal ideal of R. Since g avoids q,
localizing B_g = C_g at these primes identifies the original map R to C_q as an isomorphism.
5. Its inverse gives Spec R to Y [lem-weil-pbc-morphism-from-spec-local-ring], over X by
the same point-and-local-map classification. Spread it to a neighbourhood section by
[lem-sfb-local-ring-map-spread], using local Noetherianness and finite type from Step 1.
6. The section is a closed immersion [lem-weil-pbc-section-separated-closed-immersion].
Its image contains the unique generic point, since Step 1 identifies the generic fibre.
On an affine open of the integral source it is a quotient D to D/I
[def-weil-closed-immersion]; its image contains the zero prime, so I = 0. It is an
isomorphism, and so is the restricted f. Maximality of U gives (4).
7. Properness and Step 1 make f surjective. A finite fibre therefore has a point; finite
fibres of a locally finite-type map give quasi-finiteness there
[pqf-lem-locqf-fibre-discrete]. Apply (4), proving (3).
8. A DVR is Noetherian and normal [lem-weil-pbc-pid-noetherian-normal]. Generic stalk
isomorphisms give algebraic generic residue extensions. Apply
[lem-sfb-generically-finite-quasifinite-over-dimension-one] to get quasi-finiteness above
the codimension-one point. Singletons in that fibre are open
[lem-weil-pbc-quasi-finite-at-point-isolated]. Proper base change makes the fibre scheme
quasi-compact [def-pc-scheme-fibre, lem-weil-pbc-proper-base-change, pqf-lem-proper-basic],
so the singleton cover has a finite subcover. By [lem-trf-proper-finite-fibre-finite-near]
there is a finite restriction near the point, whose fibre is finite
[lem-weil-pbc-finite-closed-map-finite-fibres]. Apply (3), proving (2).
-/
theorem normal_modification_isomorphism_open_contains
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hgeneric : Set.BijOn f
      {η : Y | ∃ C ∈ irreducibleComponents Y, IsGenericPoint η C}
      {η : X | ∃ C ∈ irreducibleComponents X, IsGenericPoint η C})
    (hstalk : ∀ η : Y, (∃ C ∈ irreducibleComponents Y, IsGenericPoint η C) →
      IsIso (f.stalkMap η))
    (U : X.Opens) (hU : IsGreatest {V : X.Opens | IsIso (f ∣_ V)} U) :
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0 → x ∈ U) ∧
    (∀ (x : X) [IsDomain (X.presheaf.stalk x)],
      ringKrullDim (X.presheaf.stalk x) = 1 →
      IsDiscreteValuationRing (X.presheaf.stalk x) → x ∈ U) ∧
    (∀ x : X, (IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) → (f ⁻¹' {x}).Finite → x ∈ U) ∧
    (∀ x : X, (IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) →
      (∃ y : Y, f y = x ∧ f.IsQuasiFiniteAtPoint y) → x ∈ U) := by
  sorry

end AlgebraicGeometry
