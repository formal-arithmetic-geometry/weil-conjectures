/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites

/-! # Gabber's Zariski--étale restriction injectivity

Source: Stacks Project, Étale Cohomology, Tag 09ZF, first two proof paragraphs
(blueprint: lem-weil-pbc-gabber-zariski-etale-restriction-injective).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical Zariski comparison is the unique sheaf morphism compatible with
both inverse-image units, and is injective on every open.

Source: Stacks Project, Étale Cohomology, Tag 09ZF, first two proof paragraphs
(blueprint: lem-weil-pbc-gabber-zariski-etale-restriction-injective).
The isomorphisms `eX` and `eZ` identify the underlying presheaves with restriction
along the open-subscheme inclusion. The isomorphisms `a` identify the preimage
open with its scheme-theoretic fibre product; `ha` fixes their first projections.
Thus these are choices of the identifications in the node, not additional assumptions.
The global-sections factorization is the unit equation at `W = ⊤`: its middle
map is the component of `beta` on the preimage of the top open, which is all of `Z`.

Proof (the six steps of the node):
1. Restrict the étale unit to opens (lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites).
   Identify base changes of opens using lem-weil-pbc-open-immersion-base-change and
   lem-weil-pbc-morphism-factors-through-open-subscheme. Its naturality gives a
   sheaf map to the topological direct image. Adjunction
   (def-weil-pbc-topological-inverse-image and
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction) gives the unique `beta`
   satisfying the unit equation; its naturality induces maps on stalks
   (lem-weil-pbc-sets-inverse-image-stalk).
2. The étale unit is the identity-indexed colimit coprojection followed by
   sheafification (lem-weil-pbc-presheaf-pullback-sets-left-exact). Restrictions
   compose the indexing morphism, and base change preserves finite limits, so the
   index categories are filtered (lem-weil-pbc-etale-base-change-finite-limits).
3. Equality of two pulled-back sections near a point becomes local equality in
   the presheaf inverse image (lem-weil-pbc-site-sheafification-sections-local).
   Pick a covering point above it. Filtered-colimit equality gives an étale
   neighbourhood where the original sections agree
   (lem-weil-pbc-filtered-colimit-sets-elementwise). Its image is an open
   neighbourhood (lem-weil-pbc-etale-morphism-open-map); factor through this image
   (lem-weil-pbc-morphism-factors-through-open-subscheme). The surjective étale
   map to the image is a cover (lem-weil-pbc-etale-composition-cancellation,
   lem-weil-pbc-open-immersion-etale, def-weil-pbc-etale-site). The sheaf axiom
   makes the sections equal there (def-weil-pbc-etale-sheaf-of-sets and
   lem-weil-pbc-open-immersion-monomorphism).
4. Represent two inverse-image germs by sections on one common neighbourhood,
   using lem-weil-pbc-sets-inverse-image-stalk. Equality of their images gives
   equality on a smaller preimage neighbourhood by filtered-colimit equality.
   Step 3 then gives equality of the original germs, hence stalk injectivity.
5. Equal image sections have equal germs by step 4 and are equal by
   lem-weil-pbc-sheaf-sections-determined-by-germs, giving sectionwise injectivity.
6. At the top open the unit equation says restriction on global sections factors
   through the topological unit and the injective component `beta_Z`.
-/
theorem gabber_zariski_etale_restriction_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (Fzar : TopCat.Sheaf (Type (max (u + 1) v)) X.carrier)
    (eX : Fzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙ F.obj)
    (iFzar : TopCat.Sheaf (Type (max (u + 1) v)) Z.carrier)
    (eZ : iFzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        Z.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F).obj)
    (a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι))
    (ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W) :
    ∃ beta :
      (Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map i.base) (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Z.carrier)).obj Fzar ⟶ iFzar,
      (∀ V : Z.Opens, Function.Injective (beta.hom.app (op V))) ∧
      ∀ beta' :
        (Functor.sheafPullbackConstruction.sheafPullback
          (Opens.map i.base) (Type (max (u + 1) v))
          (Opens.grothendieckTopology X.carrier)
          (Opens.grothendieckTopology Z.carrier)).obj Fzar ⟶ iFzar,
        (∀ (W : X.Opens) (s : Fzar.obj.obj (op W)),
        beta'.hom.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map i.base) (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier)
            (Opens.grothendieckTopology Z.carrier)).unit.app Fzar).hom.app (op W) s) =
        eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)))) ↔ beta' = beta := by
  sorry

end AlgebraicGeometry
