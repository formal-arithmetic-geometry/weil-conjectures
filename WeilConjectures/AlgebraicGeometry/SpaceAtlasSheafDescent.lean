/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AtlasEtaleRestriction
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat

import WeilConjectures.CategoryTheory.SetSheafCoverDescent

/-!
# Descent of small étale sheaves along a scheme atlas

Source: Stacks Project, Properties of Spaces, Tag 05YY, first proof
(blueprint: lem-sfb-space-atlas-sheaf-descent).

The fibres are the actual small scheme-object étale sheaf categories. Mathlib's
descent data expresses the overlap isomorphism on every common test object. Its
universal double and triple tests are the scheme overlaps of the atlas. Thus this
uses the usual cocycle pairs, retaining their sheaf maps, rather than replacing
the local sheaf by a sheaf on an enlarged or slice site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image on the small sites of two enlarged objects is literal restriction.
Source: Stacks, Tags 03LP and 05YY
(blueprint: lem-sfb-space-atlas-sheaf-descent). -/
def atlasSmallRestriction (H : AlgebraicSpace S) {A B : H.EnlargedEtaleSite}
    (f : A ⟶ B) :
    Sheaf B.obj.left.etaleTopology (Type (max (u + 1) w)) ⥤
      Sheaf A.obj.left.etaleTopology (Type (max (u + 1) w)) :=
  (chartwiseEtaleMap f.hom.left (enlargedArrow_chartwise H f)).sheafPushforwardContinuous
    (Type (max (u + 1) w)) _ _

/-- The small étale sheaf categories with literal precomposition on arrows.
Source: Stacks, Tags 03LP, 04LY and 05YY
(blueprint: lem-sfb-space-atlas-sheaf-descent).
Restriction is strictly functorial on section presheaves. Sheaf-condition witnesses
are propositions, so they do not affect the functor identity and composition laws. -/
def atlasSmallSheafFunctor (H : AlgebraicSpace S) : H.EnlargedEtaleSiteᵒᵖ ⥤ Cat where
  obj A := Cat.of (Sheaf A.unop.obj.left.etaleTopology (Type (max (u + 1) w)))
  map f := (atlasSmallRestriction H f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The small étale sheaf categories, with their canonical restriction comparisons.
Source: Stacks, Tags 03LP, 04LY and 05YY
(blueprint: lem-sfb-space-atlas-sheaf-descent).
Both identity and composition comparisons are identity on section presheaves.
These are the composition comparisons used in the double/triple overlap cocycle. -/
def atlasSmallSheafPseudofunctor (H : AlgebraicSpace S) :
    Pseudofunctor (LocallyDiscrete H.EnlargedEtaleSiteᵒᵖ) Cat :=
  (atlasSmallSheafFunctor.{u, w} H).toPseudofunctor'

/-- The object `H/H` of the enlarged étale site, with its identity chartwise proof.
Source: Stacks, Tags 03G0 and 05YY
(blueprint: lem-sfb-space-atlas-sheaf-descent). -/
def atlasBaseObject (H : AlgebraicSpace S) : H.EnlargedEtaleSite :=
  enlargedEtaleObject (𝟙 H) (fun T a ha ↦ by simpa using ha)

/-- The unique map from an atlas object to `H/H`, retaining its original atlas map.
Source: Stacks, Tag 05YY (blueprint: lem-sfb-space-atlas-sheaf-descent). -/
def atlasToBase (H : AlgebraicSpace S) (W : H.EtaleSite) :
    (enlargedSchemeInclusion H).obj W ⟶ atlasBaseObject H :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk ⟨W.obj.hom⟩))

/-- Descent pairs for the scheme atlas, in Mathlib's intrinsic overlap formulation.
Source: Stacks, Tag 05YY (blueprint: lem-sfb-space-atlas-sheaf-descent).
The sole local object is a sheaf on `(schemeSpace W).etaleTopology`. Evaluating
`DescentData.iso` on the universal double overlap gives alpha. `pullHom_hom`
expresses pullback of that alpha, and `hom_comp` on the universal triple overlap
is precisely p23(alpha) composed with p12(alpha) equals p13(alpha). Invertibility
and that cocycle imply the diagonal identity, so `hom_self` is no extra axiom.
Morphisms are exactly the sheaf maps commuting with these isomorphisms. -/
abbrev AtlasSheafDescent (H : AlgebraicSpace S) (W : H.EtaleSite) :=
  (atlasSmallSheafPseudofunctor.{u, w} H).DescentData
    (fun _ : Unit ↦ atlasToBase H W)

/-- Restriction to the atlas with its canonical overlap isomorphism, and on maps.
Source: Stacks, Tag 05YY (blueprint: lem-sfb-space-atlas-sheaf-descent).
The pseudofunctor compares the two restrictions with their common composite to H;
thus its `ofObj` transition is exactly the canonical alpha of the statement. -/
def atlasSheafRestriction (H : AlgebraicSpace S) (W : H.EtaleSite) :
    Sheaf H.etaleTopology (Type (max (u + 1) w)) ⥤ AtlasSheafDescent.{u, w} H W :=
  (atlasSmallSheafPseudofunctor H).toDescentData (fun _ : Unit ↦ atlasToBase H W)

/-- Small étale sheaves and their maps descend along every surjective scheme atlas.
Source: Stacks Project, Properties of Spaces, Tag 05YY, first proof
(blueprint: lem-sfb-space-atlas-sheaf-descent).

Proof following the five steps of the node:
1. Use lem-trf-space-enlarged-site-scheme-density to work on the enlarged étale
   site, with terminal object H/H and singleton covering W to H. Its finite limits
   and the scheme double/triple overlaps are supplied by that density result and
   lem-trf-space-fibre-products-etale-covers. Work in the stipulated sheaf universe.
2. By lem-trf-space-enlarged-etale-ringed-site-model, extension/restriction between
   the small and enlarged sites are equivalences, and étale inverse image is
   localization restriction. Its composition comparisons give the canonical alpha.
3. Extend the local sheaf on W and lift its overlap isomorphism by full faithfulness
   on R. Faithfulness on T lifts its cocycle. The repeated singleton index retains
   the full overlap W times_H W; cancellation on the triple diagonal gives alpha=1
   on the diagonal, so Mathlib's intrinsic datum adds no hypothesis.
4. Apply lem-pe-set-sheaf-cover-descent to the singleton covering of H/H. Descend
   the extension to a sheaf on the enlarged site, then restrict to H's small site.
   The normalized comparisons give an isomorphism to the specified descent pair.
5. Lift compatible local maps by full faithfulness and glue them uniquely by the
   map clause of lem-pe-set-sheaf-cover-descent. This proves full faithfulness;
   step 4 proves essential surjectivity, hence the asserted equivalence. For a local
   isomorphism glue its inverse too; uniqueness makes both composites identities.
No quasi-compactness, separation, Noetherianity or finiteness is used. -/
theorem atlasSheafRestriction_isEquivalence (H : AlgebraicSpace S) (W : H.EtaleSite)
    (hs : IsSurjective W.obj.hom) :
    (atlasSheafRestriction.{u, w} H W).IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
