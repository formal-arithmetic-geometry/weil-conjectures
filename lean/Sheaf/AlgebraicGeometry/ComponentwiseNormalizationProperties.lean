/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.IntegralNormalGenericRecognition

/-! # Properties of componentwise normalization

Source: Stacks Project, Morphisms, Tags 035Q, 035K, 035P and 0H7D
(blueprint: lem-per-componentwise-normalization-properties).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Componentwise normalization is normal, integral, surjective, preserves component generic
points and their fibres, commutes with open restriction, and is uniquely recognized by an
integral normal cover preserving component generic points and their residue fields.
Source: Stacks Project, Morphisms, Tags 035Q (1)--(4), including the reductions footnote,
035K, 035P, and 0H7D (blueprint: lem-per-componentwise-normalization-properties).

Proof:
1. Apply lem-sfb-componentwise-normalization-generic-properties to the locally Noetherian
   scheme X. This gives domain and integrally closed stalks, integrality, surjectivity,
   the generic-point bijection, and the canonical isomorphism of each entire generic fibre
   with its residue-field spectrum. No reducedness or excellence is required.
2. Open subschemes of X are locally Noetherian by pqf-def-locnoeth. Every quasi-compact
   such open is Noetherian and has finitely many components by
   lem-weil-pbc-noetherian-finitely-many-components. Neither X nor the open U must be
   quasi-compact.
3. By lem-weil-pbc-open-immersion-base-change the pullback over U is its open inverse
   image. Apply lem-sfb-normalization-generic-residue-affine-charts on each affine
   V contained in U, both in X and U. Their stalks, residue fields, and germ maps agree:
   neighbourhoods inside an open are cofinal among all neighbourhoods of a point.
   Thus both charts are the spectrum of the same integral closure of the affine ring
   in the product of generic residue fields. The chart compatibility clause identifies
   restriction maps for each affine inclusion W contained in V. Affine opens cover
   overlaps, even when the overlaps are not affine. Glue the chart maps and their
   inverses using lem-weil-pbc-scheme-morphism-gluing. The composites are identities
   on every chart. The resulting isomorphism is over U; its uniqueness follows from
   the uniqueness of normalization maps on the component generic fields.
4. If U is normal, step 2 supplies the finite-component hypothesis of
   lem-sfb-normalization-normal-locally-finite, so its normalization map is an
   isomorphism. Composing with step 3 gives precisely the pullback projection to U.
   For empty U all charts and schemes are empty and all maps are unique.
5. For an integral f from a normal locally Noetherian Z, apply
   lem-sfb-integral-normal-generic-recognition. Its normality, generic-point bijection,
   and residue-field isomorphism hypotheses are exactly those stated here. It yields
   the unique isomorphism over X. Its target can be nonreduced, and it also permits
   empty schemes; generic stalks of a nonreduced scheme need not be fields. -/
theorem componentwiseNormalization_properties (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ((∀ x : X.reducedNormalization,
        IsDomain (X.reducedNormalization.presheaf.stalk x) ∧
          IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk x)) ∧
      IsIntegralHom X.fromReducedNormalization ∧
      Surjective X.fromReducedNormalization ∧
      Set.BijOn X.fromReducedNormalization
        {x : X.reducedNormalization |
          ∃ C ∈ irreducibleComponents X.reducedNormalization, IsGenericPoint x C}
        {x : X | ∃ C ∈ irreducibleComponents X, IsGenericPoint x C} ∧
      (∀ η : X, (∃ C ∈ irreducibleComponents X, IsGenericPoint η C) →
        IsIso (pullback.snd X.fromReducedNormalization (X.fromSpecResidueField η)))) ∧
    (∀ U : X.Opens,
      (∃! e : pullback X.fromReducedNormalization U.ι ≅ U.toScheme.reducedNormalization,
        e.hom ≫ U.toScheme.fromReducedNormalization =
          pullback.snd X.fromReducedNormalization U.ι) ∧
      ((∀ x : U.toScheme, IsDomain (U.toScheme.presheaf.stalk x) ∧
          IsIntegrallyClosed (U.toScheme.presheaf.stalk x)) →
        IsIso (pullback.snd X.fromReducedNormalization U.ι))) ∧
    (∀ (Z : Scheme.{u}) (_ : IsLocallyNoetherian Z) (f : Z ⟶ X)
      (_ : IsIntegralHom f),
      (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
        IsIntegrallyClosed (Z.presheaf.stalk z)) →
      Set.BijOn f
        {z : Z | ∃ C ∈ irreducibleComponents Z, IsGenericPoint z C}
        {x : X | ∃ C ∈ irreducibleComponents X, IsGenericPoint x C} →
      (∀ z : Z, (∃ C ∈ irreducibleComponents Z, IsGenericPoint z C) →
        IsIso (f.residueFieldMap z)) →
      ∃! e : Z ≅ X.reducedNormalization, e.hom ≫ X.fromReducedNormalization = f) := by
  sorry

end AlgebraicGeometry.Scheme
