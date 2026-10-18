/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Sheaf.AlgebraicGeometry.ProperBasic
import Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
import Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# The isomorphism open of a proper birational modification

Source: Stacks Project, Varieties, Tag 0BFP, all four clauses
(blueprint: lem-per-normal-modification-codimension-one).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The maximal isomorphism open of a proper birational map with reduced source over a
Noetherian target contains all codimension-zero points, codimension-one DVR points,
normal points with finite fibre, and normal points with a quasi-finite point above them.
Birationality is bijectivity on generic points and invertibility of the actual stalk maps
at those points. The hypotheses on `U` specify the greatest open over which `f` is an
isomorphism. A normal local ring is a normal domain, as in the source.

Source: Stacks Project, Varieties, Tag 0BFP
(blueprint: lem-per-normal-modification-codimension-one).

Proof:
1. The inverse maps on isomorphism opens are unique and glue, giving the greatest such open.
   Properness gives separatedness and finite type (`pqf-lem-proper-basic`). The source is
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`), both schemes have finitely many
   components (`lem-weil-pbc-noetherian-finitely-many-components`), and the map is locally
   finitely presented (`pqf-lem-lft-fp-locnoeth`). The birational dense-open theorem
   (`lem-per-birational-isomorphism-dense-open`) gives an isomorphism open containing every
   generic point: a dense open meets the part of each component outside the other finitely
   many components, hence contains its generic point. These are the codimension-zero points.
2. For clause (4), let `x` have normal local ring and choose a quasi-finite point `y` above it.
   The injective-germ neighbourhood (`lem-per-noetherian-injective-germ-neighbourhood`)
   makes the target integral near `x`. Properness survives restriction
   (`lem-weil-pbc-proper-base-change`). Birationality and reducedness make its inverse image
   integral (`def-pc-integral-scheme`).
3. Take affine neighbourhoods witnessing `pqf-def-quasifinite`. Shrink by principal opens
   (`lem-weil-pbc-quasi-finite-at-prime-principal-localization`). The finite-subalgebra form
   of Zariski main (`lem-weil-pbc-quasi-finite-at-finite-subalgebra-away`) supplies finite
   `A ⊆ B ⊆ C` and `g` outside the source prime with `B_g = C_g`. The generic stalk maps
   identify their fraction fields (`lem-sc-integral-function-field-affine-fraction`).
4. Affine stalk localization (`lem-weil-pbc-affine-open-stalk-localization`) identifies the
   local rings with `A_p` and `C_q`. The localized finite algebra `B_p` is integral over
   `A_p` (`lem-weil-pbc-finite-algebra-is-integral`), so normality gives `B_p = A_p` inside
   their common fraction field. Since `g` avoids `q`, localizing `B_g = C_g` then shows that
   the actual stalk map at `y` is invertible.
5. The inverse stalk map defines a section over the spectrum of the target local ring
   (`lem-weil-pbc-morphism-from-spec-local-ring`). Its composite with `f` is the canonical
   map from that spectrum. Spread it to a section over an open neighbourhood of `x`
   (`lem-per-local-ring-map-spread`).
6. This section is a closed immersion (`lem-weil-pbc-section-separated-closed-immersion`).
   Its image contains the generic point, since Step 1 makes the generic fibre a singleton.
   Hence it is surjective. In each integral affine chart its ideal contains only zero,
   since the closed image contains the zero prime (`def-weil-closed-immersion`). Thus it
   is an isomorphism, proving clause (4).
7. For clause (3), properness and Step 1 make `f` surjective: its closed image contains a
   dense open. A finite fibre is therefore nonempty, and a point in it is quasi-finite
   (`pqf-lem-locqf-fibre-discrete`). Apply clause (4).
8. For clause (2), a DVR is a PID and hence normal
   (`lem-weil-pbc-pid-noetherian-normal`). The dimension-one finiteness theorem
   (`lem-per-generically-finite-proper-near-dimension-one`) applies because the generic
   stalk maps induce algebraic residue field extensions. It makes the fibre finite
   (`lem-weil-pbc-finite-closed-map-finite-fibres`). Apply clause (3). The empty target has
   no points, so each of the four clauses is vacuous. -/
theorem normal_modification_codimension_one
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [IsReduced Y]
    (f : Y ⟶ X) [IsProper f]
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ y ∈ genericPoints Y, IsIso (f.stalkMap y))
    (U : X.Opens) (hU : IsIso (f ∣_ U))
    (hmax : ∀ V : X.Opens, IsIso (f ∣_ V) → V ≤ U) :
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0 → x ∈ U) ∧
    (∀ (x : X) [IsDomain (X.presheaf.stalk x)]
      [IsDiscreteValuationRing (X.presheaf.stalk x)],
      ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ U) ∧
    (∀ x : X, IsDomain (X.presheaf.stalk x) →
      IsIntegrallyClosed (X.presheaf.stalk x) → (f ⁻¹' {x}).Finite → x ∈ U) ∧
    (∀ x : X, IsDomain (X.presheaf.stalk x) →
      IsIntegrallyClosed (X.presheaf.stalk x) →
      (∃ y : Y, f y = x ∧ f.IsQuasiFiniteAtPoint y) → x ∈ U) := by
  sorry

end AlgebraicGeometry
