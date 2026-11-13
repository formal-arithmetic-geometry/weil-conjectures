/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleLimitSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalBaseChangeCone

/-! # Stalk of a direct image over the strict henselization

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The compatibility needed to map the base-changed strict henselization to V ×_Y X, for a
representative affine pointed neighbourhood `j` with leg `c_V` (the limit leg followed by
`Spec Γ(V, ⊤) ≅ V`). -/
theorem strictHenselizationBaseChange_condition
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    (pullback.fst (strictLocalizationToBase y) f ≫
        (strictHenselizationAffineCone y).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
              j).1.left.unop).inv) ≫
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom =
      pullback.snd (strictLocalizationToBase y) f ≫ f := by
  rw [Category.assoc, Category.assoc]
  rw [strictHenselizationStructuralMap_eq y j]
  exact pullback.condition

/-- The map X^sh → V ×_Y X with components c_V ∘ f^sh and p, for a representative affine
pointed neighbourhood `j`. -/
noncomputable def strictHenselizationBaseChangeMap
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    pullback (strictLocalizationToBase y) f ⟶
      pullback ((AffineEtale.Spec Y).obj
        ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom f :=
  pullback.lift
    (pullback.fst (strictLocalizationToBase y) f ≫
      (strictHenselizationAffineCone y).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso
          ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
            j).1.left.unop).inv)
    (pullback.snd (strictLocalizationToBase y) f)
    (strictHenselizationBaseChange_condition f y j)

/-- The site morphism σ_V from the final object to the iterated fibre product. -/
noncomputable def strictHenselizationSectionMap
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    Etale.mk (𝟙 (pullback (strictLocalizationToBase y) f)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤
        (pullback.snd (strictLocalizationToBase y) f)).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (strictHenselizationBaseChangeMap f y j) (𝟙 _)
      (pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Every direct-image germ has an affine representative, and the canonical comparison
with sections on the strict henselization pullback is the unique map with the unit and
restriction formula, and is bijective. -/
theorem sets_pushforward_stalk_strictHenselization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (H : Sheaf X.smallEtaleTopology (Type (v + 1)))
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    (∀ t : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)),
      ∃ (n : ObjectProperty.FullSubcategory
        (fun n : (pointSmallEtale y).fiber.Elements => IsAffine n.1.left))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj n.obj.1))),
        (pointSmallEtale y).toPresheafFiber n.obj.1 n.obj.2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s = t) ∧
    ∃ Θ : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) →
      ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj H).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback (strictLocalizationToBase y) f)))),
      (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          ((AffineEtale.Spec Y).obj
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))),
        Θ ((pointSmallEtale y).toPresheafFiber
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s) =
          ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj
            H).obj.map (strictHenselizationSectionMap f y j).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤
                (pullback.snd (strictLocalizationToBase y) f))
              (Type (v + 1)) (X.smallGrothendieckTopology @Etale)
              ((pullback (strictLocalizationToBase y) f).smallGrothendieckTopology
                @Etale)).unit.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((AffineEtale.Spec Y).obj
                    ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))
                s)) ∧
      Function.Bijective Θ ∧
      ∀ Θ' : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) →
        ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj H).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback (strictLocalizationToBase y) f)))),
        (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          ((AffineEtale.Spec Y).obj
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))),
        Θ' ((pointSmallEtale y).toPresheafFiber
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s) =
          ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj
            H).obj.map (strictHenselizationSectionMap f y j).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤
                (pullback.snd (strictLocalizationToBase y) f))
              (Type (v + 1)) (X.smallGrothendieckTopology @Etale)
              ((pullback (strictLocalizationToBase y) f).smallGrothendieckTopology
                @Etale)).unit.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((AffineEtale.Spec Y).obj
                    ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))
                s)) →
        Θ' = Θ := by
  classical
  let P := (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
    (X.smallGrothendieckTopology @Etale)).obj H).obj
  let F := (equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse ⋙
    strictHenselizationAffineInclusion y ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale y).fiber.Elements ↦ IsAffine n.1.left)
  let : F.Initial := (strictHenselizationAffineProperties y).1
  let B := strictHenselizationEtaleDiagram y ⋙
    MorphismProperty.Over.pullback @Etale ⊤ f
  let stalkCocone := ((pointSmallEtale y).presheafFiberCocone P).whisker F.op
  have hcStalk : IsColimit stalkCocone :=
    (Functor.Final.isColimitWhiskerEquiv F.op _).symm
      ((pointSmallEtale y).isColimitPresheafFiberCocone P)
  have hcStalk' : IsColimit (show Cocone (B.op ⋙ H.obj) from stalkCocone) := hcStalk
  obtain ⟨π, hπ, hp, hf⟩ := strictHenselizationAffineBaseChangeCone_exists f y
  let c := Cone.mk _ π
  let := (strictHenselizationAffineProperties y).2.1
  have hAff (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      IsAffine ((strictHenselizationEtaleDiagram y).obj j).left := by
    change IsAffine (Spec _)
    infer_instance
  let hComp (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      CompactSpace (B.obj j).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram y).obj j).left := hAff j
    let : CompactSpace ((strictHenselizationEtaleDiagram y).obj j).left :=
      inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace
      (Y := ((strictHenselizationEtaleDiagram y).obj j).left)
      (pullback.fst ((strictHenselizationEtaleDiagram y).obj j).hom f)
  let hQS (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      QuasiSeparatedSpace (B.obj j).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram y).obj j).left := hAff j
    let : QuasiSeparatedSpace ((strictHenselizationEtaleDiagram y).obj j).left :=
      inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated
      (Y := ((strictHenselizationEtaleDiagram y).obj j).left)
      (pullback.fst ((strictHenselizationEtaleDiagram y).obj j).hom f)
  let hTrans {j k : SmallModel.{v} (strictHenselizationNeighbourhoods y)}
      (a : j ⟶ k) : IsAffineHom (B.map a).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram y).obj j).left := hAff j
    let : IsAffine ((strictHenselizationEtaleDiagram y).obj k).left := hAff k
    change IsAffineHom (pullback.lift _ _ _)
    exact MorphismProperty.pullbackLift_fst_snd
      (P := @IsAffineHom) f
        (MorphismProperty.Over.w ((strictHenselizationEtaleDiagram y).map a)).symm
        (isAffineHom_of_isAffine
          (X := ((strictHenselizationEtaleDiagram y).obj j).left)
          (Y := ((strictHenselizationEtaleDiagram y).obj k).left) _)
  have hc := cofilteredLimitSections B c
    (pullback.snd (strictLocalizationToBase y) f) hp H hπ.some
  let e := hcStalk'.coconePointUniqueUpToIso hc.some
  have he (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      stalkCocone.ι.app (op j) ≫ e.hom =
        (limitSectionCocone B c (pullback.snd (strictLocalizationToBase y) f)
          hp H).ι.app (op j) :=
    hcStalk'.comp_coconePointUniqueUpToIso_hom hc.some (op j)
  have hσ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      limitSectionMap B c (pullback.snd (strictLocalizationToBase y) f) hp j =
        strictHenselizationSectionMap f y j := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift _ _ _ = pullback.lift _ _ _
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      change π.app j = strictHenselizationBaseChangeMap f y j
      unfold strictHenselizationBaseChangeMap
      apply pullback.hom_ext
      · exact (hf j).trans (pullback.lift_fst _ _ _).symm
      · exact (hp j).trans (pullback.lift_snd _ _ _).symm
    · simp only [pullback.lift_snd]
      rfl
  have hFormula (j : SmallModel.{v} (strictHenselizationNeighbourhoods y))
      (s : H.obj.obj (op (B.obj j))) :
      e.hom (stalkCocone.ι.app (op j) s) =
        ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj
          H).obj.map (strictHenselizationSectionMap f y j).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤
              (pullback.snd (strictLocalizationToBase y) f))
            (Type (v + 1)) (X.smallGrothendieckTopology @Etale)
            ((pullback (strictLocalizationToBase y) f).smallGrothendieckTopology
              @Etale)).unit.app H).hom.app (op (B.obj j)) s) := by
    have hs := congrArg (fun a ↦ a s) (he j)
    change e.hom (stalkCocone.ι.app (op j) s) =
      ((etaleSetPullback (pullback.snd (strictLocalizationToBase y) f)).obj
        H).obj.map (limitSectionMap B c _ hp j).op _ at hs
    rw [hσ] at hs
    exact hs
  refine ⟨?_, e.hom, hFormula, ConcreteCategory.bijective_of_isIso e.hom, ?_⟩
  · intro t
    obtain ⟨j, s, hs⟩ := Types.jointly_surjective_of_isColimit hcStalk' t
    exact ⟨(strictHenselizationAffineInclusion y).obj
      ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j.unop),
      s, hs⟩
  · intro Θ' hΘ'
    funext t
    obtain ⟨j, s, rfl⟩ := Types.jointly_surjective_of_isColimit hcStalk' t
    exact (hΘ' j.unop s).trans (hFormula j.unop s).symm

end AlgebraicGeometry
