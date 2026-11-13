/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

/-!
# Functoriality of the inverse image on small pro-étale topoi

## Main definitions

* `setPullback`: the sheafified left Kan extension on set-valued sheaves.
* `setPullbackAdjunction`: its constructed adjunction to the existing `lowerStar` on sets.
* `setPullbackComp`: the canonical composition comparison, conjugate to `lowerStarComp`.

## Main statements

* `toposFunctorialityInverseImage`: covering families, finite limits, the adjunction,
  colimits, abelian underlying sets and exactness, and compatibility of composition.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The inverse image on set-valued sheaves, as sheafified left Kan extension.

 The direct image is the existing
`lowerStar (Type (u + 1)) f`, whose definition is restriction along base change. -/
noncomputable def setPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The constructed Kan-extension/sheafification adjunction on set-valued sheaves. -/
noncomputable def setPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    setPullback f ⊣ lowerStar (Type (u + 1)) f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical composition comparison for set-valued inverse images, the conjugate of the
existing pushforward comparison. -/
noncomputable def setPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    setPullback (f ≫ g) ≅ setPullback g ⋙ setPullback f :=
  (conjugateIsoEquiv ((setPullbackAdjunction g).comp (setPullbackAdjunction f))
    (setPullbackAdjunction (f ≫ g))).symm (lowerStarComp (Type (u + 1)) f g)

/-- The geometric morphism attached to an arbitrary morphism of schemes. -/
theorem toposFunctorialityInverseImage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) ∧
      ∀ (V : Y.ProEt) (R : Presieve V), R ∈ Scheme.ProEt.precoverage Y V →
        Presieve.map (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) R ∈
          Scheme.ProEt.precoverage X
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)) ∧
    Nonempty (setPullback f ⊣ lowerStar (Type (u + 1)) f) ∧
    PreservesColimits (setPullback f) ∧
    PreservesFiniteLimits (setPullback f) ∧
    (Nonempty (upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f) ∧
      PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f)) ∧
    ∀ F : Sheaf (Scheme.ProEt.topology Z) (Type (u + 1)),
      (setPullbackAdjunction (f ≫ g)).unit.app F ≫
          (lowerStar (Type (u + 1)) (f ≫ g)).map ((setPullbackComp f g).hom.app F) =
        ((setPullbackAdjunction g).comp (setPullbackAdjunction f)).unit.app F ≫
          (lowerStarComp (Type (u + 1)) f g).hom.app
            ((setPullback g ⋙ setPullback f).obj F) := by
  have hlimits : PreservesFiniteLimits (setPullback f) := by
    have : PreservesFiniteLimits
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.lan :
          (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
      let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
        AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
      apply preservesFiniteLimits_op_lan_of_flat
    unfold setPullback Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  refine ⟨⟨inferInstance, ?_⟩, ⟨setPullbackAdjunction f⟩,
    (setPullbackAdjunction f).leftAdjoint_preservesColimits, hlimits, ⟨?_,
    inferInstance, inferInstance⟩, ?_⟩
  · intro V R hR
    obtain ⟨ι, V, a, rfl⟩ := R.exists_eq_ofArrows
    rw [Presieve.map_ofArrows]
    rw [Scheme.ProEt.mem_precoverage_iff] at hR ⊢
    rw [Presieve.map_ofArrows] at hR ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (a i).left) hR
      (pullback.fst _ f) _ (fun i ↦ pullback.fst (V i).hom f)
      fun i ↦ (MorphismProperty.Over.isPullback_map_left f (a i)).flip
  · let := Scheme.ProEt.isContinuous_overPullback f
    let : PreservesFiniteLimits
        (Functor.sheafPullbackConstruction.sheafPullback
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) := hlimits
    exact sitePullback_abelian_underlying_of_hasSheafify.{u + 1, u, 0}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
  · intro F
    exact (unit_conjugateEquiv_symm
      ((setPullbackAdjunction g).comp (setPullbackAdjunction f))
      (setPullbackAdjunction (f ≫ g))
      (lowerStarComp (Type (u + 1)) f g).hom F).symm

end AlgebraicGeometry.ProEtale
