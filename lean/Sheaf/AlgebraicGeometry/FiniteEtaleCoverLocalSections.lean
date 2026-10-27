/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteComposition
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed

/-!
# Étale local sections of a cover of a finite scheme

Source: Stacks Project, Criteria for Representability, Tag 05XQ,
lemma-surjection-space-of-sections
(blueprint: lem-sfb-finite-etale-cover-local-sections).

The fibre products are the chosen fibre products of fppf sheaves. Representable scheme
sheaves and closure of algebraic spaces under these fibre products identify these with
`Z ×_U U'` and `W ×_U U'`. The displayed pullback map is the canonical base change of `q`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable surjective étale cover of a finite scheme has a section after a
surjective étale base change on its base. No flatness of the finite map, separatedness
of the cover, or quasi-compactness of the cover is required; empty schemes are included.
Source: Stacks Project, Criteria for Representability, Tag 05XQ,
lemma-surjection-space-of-sections
(blueprint: lem-sfb-finite-etale-cover-local-sections).

Proof:
1. Representability over the scheme `Z` makes `W` a scheme. At each `u` choose an affine
   base neighbourhood and affine neighbourhoods of lifts in `W` of the finitely many
   fibre points of `Z`. Their finite disjoint union `A` and `H = Z ⨿ A` are affine.
   Use finite permanence, finite closed images and fibres, scheme coproducts, finite
   affine coproducts, and étale composition/cancellation. If the fibre is empty, remove
   the closed image of `Z` and use the empty-domain section.
2. Finite ring maps are quasi-finite, and étale maps are unramified and locally
   quasi-finite. Composition makes `H` locally quasi-finite and locally of finite type;
   its marked points are isolated in their fibres. Affineness makes its map separated.
   These use finite-ring-map-quasi-finite, unramified-quasi-finite-at-points,
   lqf-composition, lqf-locally-finite-type and affine-source-morphism-separated.
3. Apply `lem-sfb-etale-splits-isolated-purely-inseparable` to all marked points in `H`
   simultaneously. Intersect the finite clopen pieces with the original summands. This
   gives finite clopen `V_j` in `Z` and `B_l` in `A`, with singleton fibres and purely
   inseparable residue fields. A clopen part of a finite scheme is finite, since its
   ring is a quotient of a finite module. Remove the closed image of the remaining
   finite part of `Z`, whose fibre at the selected base point is empty.
4. Match each fibre point of a `V_j` with a point in some `B_l`: fibre-product points
   and faithful flatness of field extension show that the relevant tensor product of
   residue fields has a prime. The exhaustion of the marked lifts puts it in a `B_l`.
5. Intersect this `B_l` with the inverse image of `V_j`. Its map to `V_j` is finite
   by permanence over a separated target, and étale by covering base change and
   composition/cancellation. Its fibre is one point, with purely inseparable residue
   extension, since both residue fields are purely inseparable over the base field.
6. Finite-unramified-one-point-closed gives a closed immersion near that fibre point.
   The map remains étale after restriction; étale-closed-immersion-open makes it an
   isomorphism onto an open neighbourhood of the marked point of `V_j`.
7. Delete from the base the finitely many closed images of the complements of these
   neighbourhoods. The inverse maps now give sections on every clopen `V_j`. The
   coproduct universal property glues them to a section over this étale neighbourhood.
8. Take the coproduct of one such neighbourhood for every point of `U`. It is
   surjective and étale, since each summand is étale and has a lift of its point.
   Pullback and the coproduct universal property glue the local sections. Their
   section equation is checked on summands. For empty `U` use the empty coproduct;
   for empty `Z` use the identity cover and the unique empty-domain map. All maps are
   over `U`, hence over `S`, and all coproducts use the universe of the schemes. -/
theorem finite_etale_cover_local_sections {S : Scheme.{u}} (Z U : Over S)
    (p : Z ⟶ U) [IsFinite p.left] (W : AlgebraicSpace S) (q : W ⟶ schemeSpace Z)
    (hq : IsRepresentable q.hom.hom) (he : IsEtale q.hom.hom)
    (hs : IsSurjective q.hom.hom) :
    ∃ (U' : Over S) (v : U' ⟶ U), Etale v.left ∧ Surjective v.left ∧
      ∃ σ :
        Limits.pullback ((Scheme.fppfTopology.over S).yoneda.map p)
            ((Scheme.fppfTopology.over S).yoneda.map v) ⟶
          Limits.pullback (q.hom ≫ (Scheme.fppfTopology.over S).yoneda.map p)
            ((Scheme.fppfTopology.over S).yoneda.map v),
        σ ≫ Limits.pullback.map
          (q.hom ≫ (Scheme.fppfTopology.over S).yoneda.map p)
          ((Scheme.fppfTopology.over S).yoneda.map v)
          ((Scheme.fppfTopology.over S).yoneda.map p)
          ((Scheme.fppfTopology.over S).yoneda.map v)
          q.hom (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
