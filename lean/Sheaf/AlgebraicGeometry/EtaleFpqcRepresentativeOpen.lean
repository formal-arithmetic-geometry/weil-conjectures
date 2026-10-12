/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen
import Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt

/-! # Descending the agreement open of a single local representative

Source: Stacks Project, Tag 09XN, agreement-open construction before the covering argument.
(blueprint: lem-weil-pbc-etale-fpqc-representative-open). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN, paragraphs beginning "Let V" and
"By construction", and Tag 09XM, the largest agreement-open universal property.
(blueprint: lem-weil-pbc-etale-fpqc-representative-open).

Proof:
For the fixed V and t, form the largest agreement open on each T_j ×_S V
between the unit image of t and the restriction of s_j. The prescribed double
intersection equalities, transported using the unit-compatible composition
isomorphisms and fibre-product symmetry and associativity, show that the opens
have equal inverse images on all overlaps. Fpqc open descent gives an open U in V.
On T_j ×_S U the two sections agree by the universal property of the agreement
open. Unit naturality identifies the first section with the unit image of t|_U,
and functorial restriction identifies the second with s_j restricted along the
structure map. This gives the matching equation for every j.
For the image inclusion, apply unit naturality to a and π, then restrict along
the diagonal over Z. Applying this composite to hrep yields equality of the
canonical inverse-image sections used by the agreement-open universal property,
so a.left factors through the i-th agreement open. Since that open is the inverse
image of U, the map Z → V has image in U. Conversely, to recover the displayed
matching equation from equality of canonical sections, evaluate at every geometric
point of the base change of W. The inverse-image stalk comparison sends the two
germs to the original section germs; its bijectivity reflects their equality.
Geometric-germ extensionality gives the matching equation on that whole object.
This lemma treats one representative only. It asserts neither a covering of S
nor compatibility among distinct representatives. Empty Z has empty image and
places no constraint on U; empty V is handled by its unique open. -/
theorem etaleFpqcSections_descend_representative_open
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ∀ i, ((Scheme.etaleSetPullback (g i)).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (T i)))))
    (hcompat : ∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) (pullback (g i) (g j)) (g i) (pullback.fst (g i) (g j))).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
        (((Scheme.etaleSetPullback (pullback.fst (g i) (g j))).obj
            ((Scheme.etaleSetPullback (g i)).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst (g i) (g j)) (𝟙 (pullback (g i) (g j)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))).obj
                (Scheme.Etale.mk (𝟙 (T i)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))) _
            ((T i).smallGrothendieckTopology @Etale)
            ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (g i)).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 (T i)))) (s i))) =
        Eq.mp (congrArg (fun k : pullback (g i) (g j) ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j))))))
          (pullback.condition (f := g i) (g := g j)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S (T j) (pullback (g i) (g j)) (g j) (pullback.snd (g i) (g j))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
          (((Scheme.etaleSetPullback (pullback.snd (g i) (g j))).obj
              ((Scheme.etaleSetPullback (g j)).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd (g i) (g j)) (𝟙 (pullback (g i) (g j)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))).obj
                  (Scheme.Etale.mk (𝟙 (T j)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))) _
              ((T j).smallGrothendieckTopology @Etale)
              ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (g j)).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j)))))
    (i : I) (Z : (T i).Etale) (π : Z ⟶ Scheme.Etale.mk (𝟙 (T i)))
    (V : S.Etale) (a : Z ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj V)
    (t : F.obj.obj (op V))
    (hrep : ((Scheme.etaleSetPullback (g i)).obj F).obj.map π.op (s i) =
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map a.op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) (Type (u + 1))
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t)) :
    ∃ U : V.left.Opens,
      Set.range (a.left ≫ pullback.fst V.hom (g i)) ⊆ (U : Set V.left) ∧
      let W : S.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
      let b : W ⟶ V := MorphismProperty.Over.homMk U.ι rfl
      ∀ j,
        let β := MorphismProperty.Over.pullback @Etale ⊤ (g j)
        let H := (Scheme.etaleSetPullback (g j)).obj F
        let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
          ((T j).smallGrothendieckTopology @Etale)).unit.app F
        η.hom.app (op W) (F.obj.map b.op t) =
          H.obj.map (MorphismProperty.Over.homMk (β.obj W).hom
            (Category.comp_id _) : β.obj W ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j) := by
  sorry

end AlgebraicGeometry
