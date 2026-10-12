module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSubsheafFinalOpen

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 09XM, existence argument
(blueprint: lem-weil-pbc-etale-sections-equal-open-existence).
There is an open on which the two sections agree with the stated universal property.

Proof:
1. Over the small étale site of V.left, form the subpresheaf H of the terminal sheaf
   whose value on U is a singleton if the restrictions of s and t agree, and empty
   otherwise. The restriction maps exist because restriction preserves equality.
   For a covering family, compatible local sections of H say exactly that s and t
   agree on the cover. The separatedness axiom for the restricted sheaf F gives
   equality on U, hence a unique section of H. Thus H is a sheaf and H → 1 is mono.
2. Apply Scheme.existsUnique_open_of_etale_subsheaf_final (Tag 04HV) on V.left.
   It gives an open W with H(U) nonempty exactly when U → V.left factors through W.
   In particular s and t agree on W. At a geometric point x of V.left, H_x is
   nonempty exactly when the two germs agree: filteredness of pointed étale
   neighbourhoods makes equality in their colimit equivalent to equality on a common
   neighbourhood. The stalk clause of Tag 04HV therefore says x lies in W exactly
   when these germs agree.
3. For arbitrary a : T → V.left, Tag 03Q1 identifies the germs of the two displayed
   restricted sections with the germs at a(y), for each geometric point y of T.
   Their equality implies all such points map into W. Every scheme point has a
   geometric lift, so the image of a is contained in W and the open immersion
   lifting property factors a through W.
4. Conversely, if a factors through W, the map (a,id_T) factors through W ×_S T.
   Restriction compatibility of the inverse-image units transports s|_W = t|_W to
   equality on W ×_S T; further restriction along (a,id_T) gives the displayed
   equality. Steps 1 and 4 use the unit compatibility statement
   lem-weil-pbc-sets-etale-inverse-image-composition-units. -/
theorem exists_etaleSections_equal_open (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) (s t : F.obj.obj (op V)) :
    ∃ W : V.left.Opens, ∀ (T : Scheme.{u}) (a : T ⟶ V.left),
      (∃ b : T ⟶ W.toScheme, b ≫ W.ι = a) ↔
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) s) =
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) t) := by
  sorry

end AlgebraicGeometry
