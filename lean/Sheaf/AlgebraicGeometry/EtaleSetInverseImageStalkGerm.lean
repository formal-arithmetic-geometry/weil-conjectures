/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Stalks of inverse images of étale sheaves of sets, with germs

Source: Stacks Project, Étale Cohomology, Tag 03Q1 (3)
(blueprint: lem-weil-pbc-sets-etale-inverse-image-stalk-germ).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 03Q1 (3)
(blueprint: lem-weil-pbc-sets-etale-inverse-image-stalk-germ).
The unique map from the inverse-image stalk to the image-point stalk sends every germ of
a unit-pulled-back section to its original germ and is bijective. The pointed neighbourhood
on the source is the fibre product, with lift given by `pullback.lift`.

Proof:
1. By lem-weil-pbc-sets-etale-inverse-image-composition-units, the inverse image is
   presheaf pullback followed by sheafification; its unit sends a section to the
   identity-indexed colimit representative followed by sheafification. Base change is
   étale by lem-weil-pbc-etale-base-change-finite-limits.
2. Every element of a colimit of sets comes from a coprojection: the indicator of the
   union of their images agrees on all coprojections with the constant-one map, hence
   agrees everywhere by the universal property (def-weil-pbc-category-colimit).
3. By lem-weil-pbc-sets-sheafification-geometric-stalk the sheafification map induces a
   bijection on stalks. It suffices to compare the presheaf-pullback stalk to the original
   stalk, using def-weil-pbc-geometric-stalks and def-weil-pbc-pointed-etale-neighbourhoods.
4. Define alpha on a germ at (U, u) by the germ of its identity-indexed pullback section
   at the fibre-product neighbourhood (def-pc-fibre-product). Restrictions commute with
   these assignments, so the colimit universal property defines alpha on the stalk.
5. Define beta on a germ of a representative indexed by (U, phi) at (V, v) by its
   original germ at (U, p_U phi v). Transition relations and restrictions respect this
   assignment, so both colimit universal properties define beta.
6. Beta alpha is identity by the first pullback projection. Alpha beta is identity
   because phi is a morphism of pointed neighbourhoods to the fibre product. By step 2,
   checking these equalities on representatives proves them on the entire stalks.
7. Compose beta with the inverse of the sheafification-stalk bijection. The unit formula
   from step 1 gives the asserted germ formula and the composite is bijective. Every
   inverse-image stalk element is such a pulled-back germ by steps 2, 3 and 6, so any map
   satisfying the germ formula equals this one; this proves uniqueness among all maps. -/
theorem etaleSetInverseImageStalkGerm (S T : Scheme.{u}) (e : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃ c : (Scheme.pointSmallEtale t).sheafFiber.obj ((Scheme.etaleSetPullback e).obj G) →
        (Scheme.pointSmallEtale (t ≫ e)).sheafFiber.obj G,
      Function.Bijective c ∧
      (∀ (U : S.Etale) (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U)
          (a : G.obj.obj (op U)),
        c ((Scheme.pointSmallEtale t).toPresheafFiber
          ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U)
          (Over.homMk (pullback.lift x.left t (Over.w x))
            (pullback.lift_snd x.left t (Over.w x)))
          ((Scheme.etaleSetPullback e).obj G).obj
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U) a)) =
          (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber U x G.obj a) ∧
      ∀ d : (Scheme.pointSmallEtale t).sheafFiber.obj ((Scheme.etaleSetPullback e).obj G) →
          (Scheme.pointSmallEtale (t ≫ e)).sheafFiber.obj G,
        (∀ (U : S.Etale) (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U)
            (a : G.obj.obj (op U)),
          d ((Scheme.pointSmallEtale t).toPresheafFiber
            ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U)
            (Over.homMk (pullback.lift x.left t (Over.w x))
              (pullback.lift_snd x.left t (Over.w x)))
            ((Scheme.etaleSetPullback e).obj G).obj
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
              (S.smallGrothendieckTopology @Etale)
              (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U) a)) =
            (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber U x G.obj a) → d = c := by
  sorry

end AlgebraicGeometry
