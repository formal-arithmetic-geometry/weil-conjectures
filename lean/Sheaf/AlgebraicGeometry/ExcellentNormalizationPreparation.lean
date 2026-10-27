/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Integral
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Normalization preparation for reduced Noetherian excellent schemes

Source: Stacks Project, Morphisms, Tags 035S, 035Q and 0BAJ; More on Algebra,
Tags 07QV and 07QU (blueprint: lem-per-excellent-normalization-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Componentwise normalization is finite and surjective, has Noetherian excellent source
with normal local rings, and is an isomorphism over a dense open containing all generic
points of irreducible components. The empty scheme is included.

Source: Stacks Project, Morphisms, Tags 035S (lemma-nagata-normalization), 035Q
(lemma-normalization-normal) and 0BAJ (lemma-birational-isomorphism-over-dense-open);
More on Algebra, Tags 07QV and 07QU
(blueprint: lem-per-excellent-normalization-preparation).

Proof plan:
1. For empty X the component coproduct and U are empty. Otherwise, on every affine
   Spec A, lem-per-componentwise-normalization-affine-charts identifies the inverse image
   with the spectrum of the finite product of the integral closures B_i of the minimal-prime
   quotients A/p_i in their fraction fields. Each Spec B_i is an open summand.
2. Excellence implies quasi-excellence and then Nagata by lem-exc-quasi-excellent-nagata.
   By def-weil-pbc-nagata-ring and def-weil-pbc-japanese-domain, each B_i is finite over
   A/p_i, hence over A. The finite product is finite over A, proving finiteness of the
   morphism by def-weil-finite-integral-morphism.
3. The injections A/p_i into B_i are integral. Apply
   lem-weil-pbc-integral-injective-lying-over: the image of Spec B_i is V(p_i).
   These irreducible components cover Spec A, proving surjectivity.
4. By lem-weil-pbc-integral-closure-finite-extension-normal each B_i is a normal domain.
   By lem-weil-pbc-spec-domain-stalks-function-field its stalks are prime localizations;
   lem-weil-pbc-localization-normal-domain makes these integrally closed domains.
5. Each B_i is finite type over excellent A, hence excellent by
   lem-exc-finite-type-localization-excellent. Apply lem-trf-excellent-scheme-affine-cover
   to obtain excellence of every affine open of the normalization. A finite affine cover
   of X yields a finite cover of the normalization by the excellent affine summands.
   Their rings are Noetherian, so the source is locally Noetherian; the finite affine cover
   makes it quasi-compact by lem-weil-pbc-affine-scheme-qcqs.
6. By lem-weil-pbc-noetherian-finitely-many-components there are finitely many components.
   Scheme sobriety (lem-weil-pbc-scheme-sober) supplies their unique generic points.
   Around each choose an affine open avoiding all other components, using
   lem-weil-pbc-affine-opens-basis. This open is reduced and irreducible, hence integral
   by def-pc-integral-scheme, so its coordinate ring R_i is a domain.
7. Its normalization algebra C_i is finite over R_i. Multiply the nonzero denominators
   of finitely many module generators inside Frac(R_i), obtaining nonzero s_i.
   Then (C_i)_{s_i} = (R_i)_{s_i}. Use
   lem-weil-pbc-integral-closure-commutes-localization and the affine-chart description
   to identify the restriction over D(s_i) with this isomorphism. This open contains
   the component's generic point; an empty generator list gives s_i = 1.
8. Take U to be the union of these principal opens. Their inverse maps agree on overlaps
   by uniqueness of inverses and glue, including their structure-sheaf maps, to the inverse
   of the restricted normalization. U contains every component's generic point, so its
   closure contains all components and is X. Thus U is dense and has the required property.
-/
theorem excellent_normalization_preparation
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U)) :
    IsFinite X.fromReducedNormalization ∧
      Surjective X.fromReducedNormalization ∧
      IsLocallyNoetherian X.reducedNormalization ∧
      CompactSpace X.reducedNormalization ∧
      (∀ V : X.reducedNormalization.affineOpens,
        IsExcellent Γ(X.reducedNormalization, V)) ∧
      (∀ x : X.reducedNormalization,
        IsDomain (X.reducedNormalization.presheaf.stalk x) ∧
          IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk x)) ∧
      ∃ U : X.Opens, Dense (U : Set X) ∧
        (∀ Z ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η Z → η ∈ U) ∧
        IsIso (X.fromReducedNormalization ∣_ U) := by
  sorry

end AlgebraicGeometry
