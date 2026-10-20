/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.Paper.OrientedProductPointsConservative
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.IsomorphismClasses

import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
import Sheaf.TraceFormula.NormalGenericArrowTransitivity
import Sheaf.Paper.SitePointReconstructionSets
import Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Sober
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension

/-!
# Fixed-support points of the vanishing topos and the normalized stratum

Source: Orgogozo, Modifications et cycles proches sur une base générale,
proof of Lemma 8.3.2, printed p. 18 (blueprint: lem-trf-oriented-point-normalized-stratum).

The normalization is Mathlib's relative normalization of `Spec κ(s) → S`. On an affine
open containing `s`, its ring is the integral closure of `A / p_s` in `κ(s)`; on an open
missing the closure of `s` it is empty. This is precisely the normalization of the
reduced closed subscheme `closure {s}` in its function field. No finiteness is required.

The points are all geometric morphisms from sets, with direct-image natural
transformations as arrows. Isomorphism classes use Mathlib's isomorphism setoid on
the direct-image functors, pulled back to the full fixed-support subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- A topos point has support `x` if it is represented by a geometric point over `x`.
The stalk is transported by the existing equivalence of small étale presentations.
Source: Orgogozo, proof of Lemma 8.3.2, p. 18; Stacks 04HU
(blueprint: lem-trf-oriented-point-normalized-stratum). -/
def HasEtalePointSupport (X : Scheme.{u})
    (p : GeometricMorphism (Type (max (u + 1) v))
      (Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v)))) (x : X) : Prop :=
  ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (a : Spec (.of Ω) ⟶ X),
    a (IsLocalRing.closedPoint Ω) = x ∧
      Nonempty (p.inverse ≅ (etaleSheafEquivalence.{u, v} X).inverse ⋙
        (Scheme.pointSmallEtale a).sheafFiber)

/-- The objects of the full subcategory of vanishing-topos points whose second support is `s`.
Its arrows are all direct-image natural transformations, with no condition on their second
projection beyond the supports of the objects.
Source: Orgogozo, proof of Lemma 8.3.2, p. 18
(blueprint: lem-trf-oriented-point-normalized-stratum). -/
abbrev FixedSupportPoint {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :=
  {p : GeometricMorphism (Type (max (u + 1) v)) (VanishingTopos.{u, v} f) //
    HasEtalePointSupport S (p.comp (p₂ f)) s}

/-- Isomorphism classes in the full fixed-second-support subcategory. An isomorphism
of points is equivalently a natural isomorphism of their direct images, with inverse-image
mate given by `GeometricMorphism.inverseIso`.
Source: Orgogozo, the point order preceding Lemma 8.3.2, p. 18
(blueprint: lem-trf-oriented-point-normalized-stratum). -/
def fixedSupportPointSetoid {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    Setoid (FixedSupportPoint.{u, v} f s) :=
  Setoid.comap (fun p ↦ p.val.direct) (isIsomorphicSetoid _)

/-- The normalization of the reduced closure of `s`, with its map to `S`, constructed
by relative normalization in `Spec κ(s)`. Affine-locally it is the spectrum of the
integral closure of `A / p_s` in its fraction field `κ(s)`. This is the normalization
of def-sc-normalization, expressed without choosing a generic-point identification.
Source: Orgogozo, proof of Lemma 8.3.2, p. 18; Stacks 035H
(blueprint: lem-trf-oriented-point-normalized-stratum). -/
abbrev normalizedStratumMap (S : Scheme.{u}) [IsLocallyNoetherian S] (s : S) :=
  (S.fromSpecResidueField s).fromNormalization

/-- The fixed-second-support point classes are the Zariski points of the normalized
base change, compatibly with first support and with every point arrow, including
noninvertible ones. The last clause states antisymmetry on isomorphism classes.
Source: Orgogozo, proof of Lemma 8.3.2, printed p. 18
(blueprint: lem-trf-oriented-point-normalized-stratum).

Proof (the seven steps of the DAG):
1. The étale-point classification and oriented-product universal property represent
   points by triples `(a,b,u)` with `u : b ⇒ f(a)`, retaining the arrow as data.
2. Arrows between triples are compatible pairs of arrows on the two factors.
   On triple-site generators use the fibre pullback formula; the set-valued point
   reconstruction colimit extends the resulting germ maps uniquely to all sheaves.
3. The support-fibre equivalence for `Spec κ(s) → S` identifies the full subcategory
   with the points of `X_Et ←×_S (Spec κ(s))_Et`, fully faithfully on all arrows.
4. A locally Noetherian scheme is quasi-separated. Normalization in the identity
   residue-field extension gives the integral normal base `N_s` and its generic inclusion.
   Integral middle-base equivalence (Orgogozo Lemma 8.3.1) identifies this oriented
   product with `(X ×_S N_s)_Et ←×_(N_s) (Spec κ(s))_Et`, preserving first support.
5. Choose an algebraic closure of the generic residue field. Every point of the base
   change admits a geometric representative and an arrow from this generic point.
   Normal-generic arrow transitivity aligns any two arrows over the same support.
   Full faithfulness for the generic residue inclusion lifts its automorphism to
   `Spec κ(s)`. The compatible pair is an isomorphism of triples. Thus supports give
   the asserted bijection, independently of geometric representatives.
6. An arrow `q ⇒ p` restricts on open subterminals to the Zariski specialization from
   its first support at `q` to its first support at `p`. Conversely a specialization
   lifts the geometric generization to the strict localization of the specialization.
   Point reconstruction gives its germ map; normal-generic transitivity aligns the
   generic arrows, and support-fibre full faithfulness lifts the correcting automorphism.
   The resulting compatible pair gives the required arrow of triples.
7. Mutual specialization gives the same generic point of the common singleton closure
   by sobriety of schemes, so the bijection implies equality of point classes.
No finite-type condition on `f`, nor finiteness of the normalization, enters these steps. -/
theorem oriented_point_normalized_stratum
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [CompactSpace S] (s : S) :
    ∃ θ : Quotient (fixedSupportPointSetoid.{u, v} f s) ≃
        ↥(pullback f (normalizedStratumMap S s)),
      (∀ p : FixedSupportPoint.{u, v} f s,
        HasEtalePointSupport X (p.val.comp (p₁ f))
          (pullback.fst f (normalizedStratumMap S s)
            (θ (Quotient.mk (fixedSupportPointSetoid f s) p)))) ∧
      (∀ p q : FixedSupportPoint.{u, v} f s,
        Nonempty (q.val.direct ⟶ p.val.direct) ↔
          θ (Quotient.mk (fixedSupportPointSetoid f s) p) ∈
            closure {θ (Quotient.mk (fixedSupportPointSetoid f s) q)}) ∧
      (∀ p q : FixedSupportPoint.{u, v} f s,
        Nonempty (q.val.direct ⟶ p.val.direct) →
        Nonempty (p.val.direct ⟶ q.val.direct) →
        Quotient.mk (fixedSupportPointSetoid f s) p =
          Quotient.mk (fixedSupportPointSetoid f s) q) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
