/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.GabberH0ZariskiConstructions
public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Global transport through the composition comparison

Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs.
(blueprint: lem-weil-pbc-gabber-h0-zariski-target-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The chosen global transport agrees with section comparison through the other
side of the pullback square.
Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs; Sites,
Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-target-comparison).

Proof: Expand the inverse defining the target section and the section isomorphism.
The latter first identifies the top open with the twice-pulled-back identity,
then applies the composition comparison for h and the second projection, and
then the fibre-product pasting isomorphism. Naturality of that comparison moves
these identifications to the composite inverse image. Their composite is the
canonical top-to-identity-pullback isomorphism: compose with each fibre-product
projection to check this by pullback uniqueness. Cancel the inverse of the
section isomorphism. The remaining equality transport is along pullback.condition;
the definition of section comparison along the first projection has exactly the
same transport and pasting map. Equality elimination and proof irrelevance identify
the transports. The result is an identity of functions on sections, so also applies
to empty schemes and to sheaves having no global sections. -/
theorem gabberZariskiTargetComparison
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj
        (Scheme.Etale.mk (𝟙 X))))) :
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h (pullback.snd i h)).hom.app F).hom.app
        (op (Scheme.Etale.mk (⊤ : (pullback i h).Opens).ι)))
          (gabberZariskiTargetSection i h F t) =
      ((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
        (gabberTopPullbackIso (pullback.snd i h ≫ h)).hom.op
          (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
            pullback.condition F (Scheme.Etale.mk (𝟙 X)) t) := by sorry

end AlgebraicGeometry
