/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
public import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation

/-! # Lifted compatible atlases for infinitesimal space pushouts

Source: Stacks Project, spaces-pushouts.tex, Tag 07VX,
`lemma-pushout-along-thickening`; Tags 07W0 and 07W2, `equation-cube-over`
(blueprint: lem-sfb-space-pushout-lifted-atlas).

The overlap is the actual sheaf fibre product. Its specified isomorphism over `T`
determines the map to `W`. The conclusion supplies a representing scheme `D`, its
scheme pushout `Q`, and the unique extension `Q → P`, which is surjective étale.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A compatible pair of scheme atlases yields a surjective étale scheme atlas of the
space pushout. The equations for `e` specify both maps of the overlap using the given
`φ`, rather than replacing that identification by an arbitrary isomorphism.
Source: Stacks Project, Tag 07VX, quotient construction with prescribed atlases;
Tags 07W0 and 07W2, northeast atlas arrow in `equation-cube-over`
(blueprint: lem-sfb-space-pushout-lifted-atlas).

Proof:
1. Represent `V ×_S T` by `D`, affine over `V`, using the affine scheme tests for `a`.
   The specified `φ` identifies its map to `W` with a base change of `i`, hence a
   thickening by lem-sfb-space-thickening-base-change. The scheme pushout node
   lem-sfb-scheme-affine-thickening-pushout gives `Q = V amalg_D W`. By
   lem-sfb-space-affine-thickening-pushout it is also a pushout against space targets,
   giving the unique extension to `P`.
2. Form the scheme kernel pairs R_V, R_W and R_D of the three chart maps, using
   lem-trf-space-representable-etale-scheme-tests. Associativity and `φ` identify
   R_D with the restrictions of R_V and R_W over `T`. Its map to R_V is affine,
   and its map to R_W is a thickening by lem-sfb-space-thickening-base-change.
   Form their scheme pushout `R`, with two induced projections to `Q`.
3. Both projections are étale by lem-sfb-scheme-infinitesimal-etale-patching applied
   to the kernel-pair projections. Its canonical unit identifies their restrictions
   to `V` and `W` with R_V and R_W, respecting the prescribed overlap.
4. Glue kernel-pair diagonals and flips using the scheme pushout. For composition,
   the scheme `R ×_Q R` is étale over `Q`. The projection-compatible identifications
   of step 3 identify its restrictions with the two kernel-pair composition domains.
   The canonical étale patching counit presents it as their scheme pushout. Glue
   composition and check source and target on the two pushout pieces.
5. On algebraically closed field points, the thickenings V into Q and R_V into R
   induce bijections: maps to fields kill every element of the nil defining ideals.
   Thus the geometric relation is the kernel equivalence relation of V over S.
   With the operations of step 4, lem-sfb-unramified-geometric-equivalence-relation
   makes R an equivalence relation. By lem-trf-etale-relation-quotient, F = Q/R is
   an algebraic space and its quotient map is representable surjective étale.
6. The maps V to F and W to F coequalize their kernel pairs. Descend them to S and
   T' by lem-a1-etale-atlas-presentation and the quotient universal property. They
   agree on T, as can be checked after the surjective étale cover D to T and then
   descended using the sheaf axiom in def-trf-algebraic-space.
7. A compatible pair S to L and T' to L gives a unique map Q to L by the space
   pushout property for scheme spans in lem-sfb-space-affine-thickening-pushout.
   Its two composites from R agree on R_V and R_W, hence agree by that same
   property for R. The quotient universal property gives the unique map F to L.
   Check its restrictions and uniqueness after the two original atlases using
   lem-a1-etale-atlas-presentation. Thus F is a pushout of the original span.
8. Pushout uniqueness identifies F with P compatibly with the two pieces. The
   composite of Q to F with this isomorphism is the unique extension Q to P.
   It is representable surjective étale by lem-trf-etale-relation-quotient and
   lem-trf-space-representable-etale-scheme-tests. All constructions permit empty
   schemes and nil ideals without a bounded exponent. -/
theorem spacePushout_liftedAtlas {B : Scheme.{u}}
    (T T' S P : AlgebraicSpace B) (i : T ⟶ T') (a : T ⟶ S)
    (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom)
    (hP : IsPushout a i j b)
    (V W : Over B) (v : schemeSpace V ⟶ S) (w : schemeSpace W ⟶ T')
    (hv : IsEtale v.hom.hom) (hvSurj : IsSurjective v.hom.hom)
    (hw : IsEtale w.hom.hom) (hwSurj : IsSurjective w.hom.hom)
    (φ : Limits.pullback v.hom a.hom ≅ Limits.pullback w.hom i.hom)
    (hφ : φ.hom ≫ Limits.pullback.snd w.hom i.hom =
      Limits.pullback.snd v.hom a.hom) :
    ∃ (D : Over B) (e : (schemeSpace D).obj ≅ Limits.pullback v.hom a.hom)
      (dV : D ⟶ V) (dW : D ⟶ W),
      e.hom ≫ Limits.pullback.fst v.hom a.hom =
        (Scheme.fppfTopology.over B).yoneda.map dV ∧
      (e.hom ≫ φ.hom) ≫ Limits.pullback.fst w.hom i.hom =
        (Scheme.fppfTopology.over B).yoneda.map dW ∧
      IsAffineHom dV.left ∧
      ∃ (Q : Over B) (jV : V ⟶ Q) (jW : W ⟶ Q),
        IsPushout dV.left dW.left jV.left jW.left ∧
        ∃ q : schemeSpace Q ⟶ P,
          (Scheme.fppfTopology.over B).yoneda.map jV ≫ q.hom = v.hom ≫ j.hom ∧
          (Scheme.fppfTopology.over B).yoneda.map jW ≫ q.hom = w.hom ≫ b.hom ∧
          IsEtale q.hom.hom ∧ IsSurjective q.hom.hom ∧
          ∀ q' : schemeSpace Q ⟶ P,
            (Scheme.fppfTopology.over B).yoneda.map jV ≫ q'.hom = v.hom ≫ j.hom →
            (Scheme.fppfTopology.over B).yoneda.map jW ≫ q'.hom = w.hom ≫ b.hom →
            q' = q := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
