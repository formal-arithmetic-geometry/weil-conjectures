/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Maps from a quasi-coherent source on a smooth atlas

Source: Stacks Project, stacks-sheaves.tex, Tag 076S, lemma-map-from-quasi-coherent;
algebraic.tex, Tags 04T5 and 04WY
(blueprint: lem-sfb-smooth-atlas-quasicoherent-source-maps).

Restrictions below retain their underlying module presheaves on the small etale sites.
The forgetful functor from module sheaves is fully faithful, so their Hom sets are
unchanged. The comparison diagram is stated on every chart and every local tensor
representative. This avoids inverting any comparison for the arbitrary target module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite
open AlgebraicGeometry

namespace CategoryTheory

/-- Restrict a big-fppf module to the etale scheme charts of an algebraic space mapping
to the stack. This is literal precomposition on modules and on regular-function rings.
Its values are the underlying module presheaves of the small-etale restrictions;
no sheafification or cartesian replacement of the module is performed.
Source: Stacks 076S, the restrictions in its comparison diagram
(blueprint: lem-sfb-smooth-atlas-quasicoherent-source-maps). -/
def moduliEtaleChartRestriction {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    (X : AlgebraicSpace S) (a : BasedFunctor (discreteModuli X.obj.obj) C) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      PresheafOfModules.{max (u + 1) v w}
        ((ObjectProperty.ι (fun T : CostructuredArrow yoneda X.obj.obj ↦
          AlgebraicSpace.IsEtale T.hom) ⋙ a.toFunctor).op ⋙
            (moduliModuleRings C hC).obj) :=
  SheafOfModules.forget (moduliModuleRings C hC) ⋙
    PresheafOfModules.pushforward₀ (ObjectProperty.ι
      (fun T : CostructuredArrow yoneda X.obj.obj ↦ AlgebraicSpace.IsEtale T.hom) ⋙
        a.toFunctor)
      (moduliModuleRings C hC).obj

/-- The canonical object on the atlas self-relation, using its first projection.
The isomorphism in the existing 2-fibre product identifies it with the second one.
Source: Stacks 04T5 and 076S
(blueprint: lem-sfb-smooth-atlas-quasicoherent-source-maps). -/
def moduliAtlasRelationObject {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} {U : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) C) (R : AlgebraicSpace S)
    (e : BasedFunctor (discreteModuli R.obj.obj) (moduliTwoFiberProduct a a)) :
    BasedFunctor (discreteModuli R.obj.obj) C :=
  (e.comp (moduliTwoFiberFst a a)).comp a

/-- The commutative tensor-comparison diagram, evaluated on all local tensors.
Here `d` is the common map G_R to H_R. For each etale chart V of R and each etale
chart W of U, the first (respectively second) equation says that d sends the
restriction of s along p1 (respectively p2) to the restriction of b(s). These
are the comparison maps on 1 tensor s; linearity gives the formula on r tensor s.
All factorizations V to W are included, as in the chart-limit definition of direct
image in def-trf-space-etale-module-functors. Consequently the adjunction defining
tensor pullback identifies these two equations with
`c1G ≫ d = p1*b ≫ c1H` and `c2G ≫ d = p2*b ≫ c2H`.
The source comparisons are isomorphisms by
lem-sfb-stack-quasi-coherent-scheme-restriction, so existence of d is equivalent
to the node's equation with delta_G = c1G followed by inverse c2G.
Source: Stacks 076S, displayed commutative diagram
(blueprint: lem-sfb-smooth-atlas-quasicoherent-source-maps). -/
def ModuliAtlasMapCompatible {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) C)
    (R : AlgebraicSpace S)
    (e : BasedFunctor (discreteModuli R.obj.obj) (moduliTwoFiberProduct a a))
    (G H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
    (b : (moduliEtaleChartRestriction hC (AlgebraicSpace.schemeSpace U) a).obj G ⟶
      (moduliEtaleChartRestriction hC (AlgebraicSpace.schemeSpace U) a).obj H) : Prop :=
  ∃ d : (moduliEtaleChartRestriction hC R (moduliAtlasRelationObject a R e)).obj G ⟶
      (moduliEtaleChartRestriction hC R (moduliAtlasRelationObject a R e)).obj H,
    (∀ (V : R.EtaleSite) (W : (AlgebraicSpace.schemeSpace U).EtaleSite)
      (f : (e.toFunctor.obj V.obj).obj.left ⟶ W.obj)
      (s : G.val.obj (op (a.toFunctor.obj W.obj))),
      d.app (op V) (G.val.map (a.toFunctor.map f).op s) =
        H.val.map (a.toFunctor.map f).op (b.app (op W) s)) ∧
    (∀ (V : R.EtaleSite) (W : (AlgebraicSpace.schemeSpace U).EtaleSite)
      (f : (e.toFunctor.obj V.obj).obj.right ⟶ W.obj)
      (s : G.val.obj (op (a.toFunctor.obj W.obj))),
      d.app (op V)
        (G.val.map ((e.toFunctor.obj V.obj).obj.hom ≫ a.toFunctor.map f).op s) =
      H.val.map ((e.toFunctor.obj V.obj).obj.hom ≫ a.toFunctor.map f).op
        (b.app (op W) s))

/-- Restriction is injective with image precisely the compatible atlas maps, hence
is a bijection onto that subset and gives unique extension of each such map.
The relation is any algebraic-space presentation of the actual 2-fibre product;
`he` identifies it with U times_C U, including its canonical two projections.
Only G is required to be quasi-coherent.

Source: Stacks Project, Tag 076S, via 04T5 and 04WY
(blueprint: lem-sfb-smooth-atlas-quasicoherent-source-maps).

Proof:
1. By def-sfb-algebraic-moduli-stack, scheme base changes of the atlas are smooth
surjective algebraic spaces. Their etale scheme charts are smooth, hence flat and
locally of finite presentation by lem-pc-smooth-flat. Part (2) of
lem-sfb-fppf-groupoid-stack-presentations gives its self-relation groupoid and an
equivalence [U/R] to C commuting with the atlas. R remains an algebraic space.
2. Precompose G and H with this equivalence. A based equivalence preserves underlying
schemes, covering families and regular functions, so precomposition with its inverse
and the unit/counit give inverse module equivalences. The local free presentations
of G are preserved, as are all etale restrictions and canonical tensor comparisons.
3. Apply lem-sfb-groupoid-maps-from-quasicoherent to these transferred modules. It
makes restriction injective and identifies its image with equality of the maps from
G_R obtained by inverse source comparisons, pullback of b and target comparisons.
The target module is arbitrary; only the source comparisons are inverted.
4. Compose that equality with c1G to obtain the node's delta_G equation. Equivalently,
there is a common map d from G_R to H_R making both comparison squares commute.
By the tensor/direct-image adjunction these squares are precisely the two families
of section equations in ModuliAtlasMapCompatible: the unit is 1 tensor s and
linearity gives all local tensors. Full faithfulness of forgetting the sheaf
condition leaves the atlas and relation Hom sets unchanged. Transfer back to C.
No quasi-compactness, finiteness, Deligne--Mumford, or hypothesis on H is used. -/
theorem smoothAtlas_quasicoherent_source_maps {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C)
    (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) C)
    (ha : IsSmoothModuliAtlas C U a) (R : AlgebraicSpace S)
    (e : BasedFunctor (discreteModuli R.obj.obj) (moduliTwoFiberProduct a a))
    (he : e.toFunctor.IsEquivalence)
    (G H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1))
    (hG : G.IsQuasicoherent) :
    Function.Injective
      ((moduliEtaleChartRestriction hC.1.1 (AlgebraicSpace.schemeSpace U) a).map
        (X := G) (Y := H)) ∧
    ∀ b : (moduliEtaleChartRestriction hC.1.1 (AlgebraicSpace.schemeSpace U) a).obj G ⟶
        (moduliEtaleChartRestriction hC.1.1 (AlgebraicSpace.schemeSpace U) a).obj H,
      (∃ f : G ⟶ H,
        (moduliEtaleChartRestriction hC.1.1 (AlgebraicSpace.schemeSpace U) a).map f = b) ↔
          ModuliAtlasMapCompatible hC.1.1 a R e G H b := by
  sorry

end CategoryTheory
