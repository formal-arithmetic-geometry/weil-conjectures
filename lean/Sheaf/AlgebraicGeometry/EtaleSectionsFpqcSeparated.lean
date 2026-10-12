/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen

/-! # EtaleSectionsFpqcSeparated

Source: Stacks Project, Tag 09XN
(blueprint: lem-weil-pbc-etale-sections-fpqc-separated). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN, uniqueness, and Tag 03S2, identity restriction.
(blueprint: lem-weil-pbc-etale-sections-fpqc-separated).

Proof:
Apply the largest agreement open theorem to the identity etale object and the
two global sections. Equality of their pullbacks factors every g_i through the
agreement open. An fpqc covering is jointly surjective, so every point of S lies in
this open, which is therefore all of S. Test its universal property on the identity
of S. Inverse image along the identity is canonically restriction along the identity;
the unit followed by restriction along the diagonal is the identity section map.
Thus equality after this identity pullback gives equality of the original sections.
This also handles an empty base or an empty indexing type whenever it is a cover. -/
theorem etaleSections_eq_of_fpqc_pullbacks
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (t t' : F.obj.obj (op (Scheme.Etale.mk (𝟙 S))))
    (heq : ∀ i,
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map
        (MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
          Scheme.Etale.mk (𝟙 (T i)) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (Scheme.Etale.mk (𝟙 S))).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) _
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t) =
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map
        (MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
          Scheme.Etale.mk (𝟙 (T i)) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (Scheme.Etale.mk (𝟙 S))).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) _
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t')) : t = t'  := by
  sorry

end AlgebraicGeometry
