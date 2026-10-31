/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Maps.Basic
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.SeparatedEtaleChart
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A dense open scheme in a relatively quasi-separated algebraic space

Source: Stacks Project, Decent Spaces, Tags 086U and 03JX; Properties of Spaces,
Tags 03JH and 07S4 (blueprint: lem-sfb-quasiseparated-space-dense-scheme-open).

The hypothesis tests the relative diagonal over the arbitrary base scheme on schemes.
The conclusion uses the existing residue-field point map and atlas topology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space whose relative diagonal is quasi-compact on scheme tests has a
scheme open subspace with dense image, including when the space is empty.

Source: Stacks Project, Decent Spaces, Tag 086U (theorem-decent-open-dense-scheme),
Tag 03JX (lemma-bounded-fibres), and Tag 03JI (proposition-reasonable-open-dense-scheme);
Properties of Spaces, Tags 03JH and 07S4.
(blueprint: lem-sfb-quasiseparated-space-dense-scheme-open).

Proof:
1. Take the largest schematic open V using lem-sfb-space-largest-schematic-open.
   For any nonempty open O of Y, lem-a1-space-etale-open-image realizes O as an
   open subspace. By lem-a1-space-affine-atlas-open-cover choose inside O a nonempty
   open X with affine surjective etale atlas U and a map to an affine open B of S.
2. The relation R = U ×_X U maps to U ×_B U by a pullback of the relative diagonal
   of Y. This identifies scheme tests using lem-trf-space-fibre-products-etale-covers.
   The target is affine by lem-weil-pbc-fibre-product-affine-spectra, and compact by
   lem-weil-pbc-affine-scheme-qcqs. The diagonal hypothesis makes R compact.
   By lem-weil-pbc-qcqs-morphism-permanence its projection to U is quasi-compact;
   lem-sfb-space-qs-atlas-criterion makes X absolutely quasi-separated.
3. By lem-sfb-space-qc-etale-fibre-bound the geometric fibre sizes of U → X are
   bounded. The atlas is quasi-compact by lem-sfb-space-qcqs-permanence, and separated
   by lem-weil-pbc-affine-source-morphism-separated and lem-a1-separated-etale-chart.
   Hence lem-sfb-space-etale-closed-degree-loci gives closed loci D_r of degree ≤ r.
4. The attained positive degrees have a maximum d. The complement T of D_(d-1) is
   nonempty open with constant degree d. Use lem-a1-space-etale-open-image to realize
   it as an open subspace. Its atlas remains surjective etale by
   lem-trf-space-fibre-products-etale-covers, quasi-compact by
   lem-sfb-space-quasicompact-affine-tests, and separated by
   lem-weil-pbc-closed-immersion-base-change applied to the atlas diagonal.
5. By lem-sfb-space-constant-degree-etale-finite the restricted atlas is finite locally
   free. Its source is an open subscheme of affine U, so
   lem-sfb-finite-locally-free-open-affine-cover makes T a scheme. Thus T lies in V.
6. Every nonempty open meets V, proving density. By lem-a1-space-point-open-calculus
   its canonical point map is a homeomorphism onto its open image. Its S-structure
   is the composite through Y. For empty Y take its empty schematic open; density
   is vacuous, and the positive-degree selection is unnecessary. -/
theorem exists_dense_scheme_open {S : Scheme.{u}} (Y : AlgebraicSpace S)
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj))) :
    ∃ (V : Over S) (j : yoneda.obj V ⟶ Y.obj.obj),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j ∧
      Topology.IsOpenEmbedding (schemePointMap j) ∧ DenseRange (schemePointMap j) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
