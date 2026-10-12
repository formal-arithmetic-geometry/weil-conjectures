/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.GabberH0ZariskiConstructions
public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Local transport through the composition comparison

Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The local representative calculation before identifying the global target section.
Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs;
Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-local-comparison).

Proof: Let j be the second projection and k = j followed by h. Naturality of the
unit for j moves the representative's restriction through that unit. Naturality
of the composition isomorphism then moves the preimage-open restriction through
its component. The composition-unit equation identifies the result with the
unit for k restricted along d, where d is the preimage-open map followed by the
base change of pullback.lift phi W.ι hphi and the inverse pasting isomorphism.
The composition-unit equation along the first projection identifies that unit
with the section comparison applied to the unit for i. Substitute hs. Naturality
of section comparison with respect to the map U to the identity object gives
the restriction of the compared global section along d followed by the base
change of U to X. This map equals the top-open inclusion followed by the canonical
identity-pullback isomorphism: both are over the same scheme and the second
projection of the identity pullback is an isomorphism, so cancellation proves
equality. Presheaf functoriality gives the two restrictions on the right. This
calculation needs neither a closed immersion nor a covering, and remains valid
for empty opens. -/
theorem gabberZariskiLocalComparison
    {X Z U X' : Scheme.{u}} (i : Z ⟶ X)
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s : F.obj.obj (op (Scheme.Etale.mk q)))
    (hs : etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
      ((Scheme.etaleSetPullback i).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ i).map
          (MorphismProperty.Over.homMk q (Category.comp_id q) :
            Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    (W : X'.Opens) (phi : W.toScheme ⟶ U) (hphi : phi ≫ q = W.ι ≫ h)
 :
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h (pullback.snd i h)).hom.app F).hom.app
        (op (Scheme.Etale.mk ((pullback.snd i h) ⁻¹ᵁ W).ι)))
          (((Scheme.etaleSetPullback (pullback.snd i h)).obj
            ((Scheme.etaleSetPullback h).obj F)).obj.map
              (gabberPreimageEtaleIso (pullback.snd i h) W).hom.op
              (etaleSetDescentUnit (pullback.snd i h) ((Scheme.etaleSetPullback h).obj F)
                (Scheme.Etale.mk W.ι) (gabberLocalRepresentative q h F s W phi hphi))) =
      ((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
        ((gabberOpenEtale (pullback i h)).map (homOfLE le_top)).op
        (((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
          (gabberTopPullbackIso (pullback.snd i h ≫ h)).hom.op
          (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
            pullback.condition F (Scheme.Etale.mk (𝟙 X)) t)) := by sorry

end AlgebraicGeometry
