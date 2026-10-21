/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Nested summands in section-preserving support composition

Source: Stacks Project, Tags 0F4Y and 0F50
(blueprint: lem-sfb-etale-support-nested-summands).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The structural summand inclusion followed by the ordinary direct-image comparison
is the graph extension. This converts the summand equation to an equality of sections. -/
private lemma unit_comp_toLowerStar
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : X.Etale) :
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).unit.app M).hom.app
        (Opposite.op W) ≫
      (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) =
      Scheme.Etale.graphExtend f M W := by
  have h := (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv
    M _ |>.apply_symm_apply ((lowerStarUnit (ModuleCat.{u + 1} A) f).app M)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.hom.app (Opposite.op W)) h

private lemma unit_comp_normalized_inclusion
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ι : F ⟶ lowerStar (ModuleCat.{u + 1} A) f)
    (o : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ F)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (n : o.hom.app M ≫ ι.app M = etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M)
    (W : X.Etale) :
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).unit.app M).hom.app
        (Opposite.op W) ≫
      (o.hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) ≫
      (ι.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) =
      Scheme.Etale.graphExtend f M W := by
  have hn := congrArg (fun k => k.hom.app
    (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W))) n
  change (o.hom.app M).hom.app _ ≫ (ι.app M).hom.app _ = _ at hn
  rw [hn]
  exact unit_comp_toLowerStar A f M W

/-- The composition determined inside direct image sends a pair of etale lifts to their
composite lift.
Source: Stacks Project, Tags 0F4Y and 0F50
(blueprint: lem-sfb-etale-support-nested-summands).

Proof: postcompose the two arrows with the injective support inclusion on the final
etale test object. Substitute the three sum-to-direct-image normalization equations and
the section-preserving equation of sigma. The adjunction units select the summands
indexed by the structural lifts. Extending first along the inner graph and then along
the outer graph gives the extension along the composite graph: the sections agree on
that graph and are zero on its clopen complement. The sheaf axiom proves equality;
linearity and sheafification extend it from generators. The mapComp inverse is the
canonical identification of the two composite test objects. Injectivity cancels the
postcomposition and proves the claimed equation. -/
theorem etaleSupportNestedSummands
    (A : Type (u + 1)) [CommRing A]
    {V T B : Scheme.{u}} (h : V ⟶ T) (e : T ⟶ B) [Etale h] [Etale e]
    [IsSeparated h] [IsSeparated e]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ιh : F ⟶ lowerStar (ModuleCat.{u + 1} A) h)
    (ιe : G ⟶ lowerStar (ModuleCat.{u + 1} A) e)
    (ιhe : H ⟶ lowerStar (ModuleCat.{u + 1} A) (h ≫ e))
    (hi : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : B.Etale),
      Function.Injective ((ιhe.app M).hom.app (Opposite.op W)))
    (oh : etaleLowerShriek (ModuleCat.{u + 1} A) h inferInstance ≅ F)
    (oe : etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ≅ G)
    (ohe : etaleLowerShriek (ModuleCat.{u + 1} A) (h ≫ e) inferInstance ≅ H)
    (nh : ∀ M, oh.hom.app M ≫ ιh.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) h M)
    (ne : ∀ M, oe.hom.app M ≫ ιe.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M)
    (nhe : ∀ M, ohe.hom.app M ≫ ιhe.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) (h ≫ e) M)
    (σ : F ⋙ G ≅ H)
    (nσ : ∀ M, σ.hom.app M ≫ ιhe.app M =
      ιe.app (F.obj M) ≫ (lowerStar (ModuleCat.{u + 1} A) e).map (ιh.app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
              (Opposite.op W) ≫
            (oh.hom.app M).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              (F.obj M)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            (oe.hom.app (F.obj M)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app M).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app M).hom.app (Opposite.op W) ≫
            (ohe.hom.app M).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            (H.obj M).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op := by
  sorry

end AlgebraicGeometry.Etale
