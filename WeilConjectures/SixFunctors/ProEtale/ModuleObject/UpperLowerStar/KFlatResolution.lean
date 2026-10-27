/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.SeparatorResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMapMod
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.CategoryTheory.Generator.SheafFreeYonedaPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# K-flat resolutions preserved by the pullback of module objects

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. We show that
every complex `K` of `Λ_Y`-modules receives a quasi-isomorphism `Q ⟶ K` from a K-flat complex
`Q` such that the pullback `mapMod(f^*) Q` is a K-flat complex of `f^* Λ_Y`-modules
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_quasiIso_kFlat_mapMod_upperStar`). This is
the resolution input of `CategoryTheory.Functor.preservesKFlatComplexes_of_exists_quasiIso`.

The resolutions are built from the free modules `Λ_Y ⊗ G_Y`, where `G_Y = ⊕_V ℤ[V]` is the
direct sum of the free abelian sheaves on all objects `V` of the small pro-étale site of `Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.freeSeparator`). It is a flat separator of the
category of abelian pro-étale sheaves on `Y`, and its pullback is
`f^* G_Y ≅ ⊕_V ℤ[V ×_Y X]`, since `f^* ℤ[V] ≅ ℤ[V ×_Y X]`
(`CategoryTheory.Sheaf.freeYonedaPullbackIso`);
hence `f^* G_Y` is flat as well. Consequently `Λ_Y ⊗ G_Y` is a flat separator of `Mod_{Λ_Y}`
whose pullback `f^* Λ_Y ⊗ f^* G_Y` is flat, and
`CategoryTheory.Functor.exists_quasiIso_kFlat_mapHomologicalComplex_kFlat` applies.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section FreeSeparator

instance (Z : Scheme.{u}) (T : Type (u + 1)) :
    HasColimitsOfShape (Discrete T) (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} _ _

variable (Y : Scheme.{u})

/-- The free abelian sheaf `ℤ[V]` on an object `V` of the small pro-étale site is flat. -/
lemma flat_freeYoneda (V : Y.ProEt) :
    ObjectProperty.flat (Sheaf.freeYoneda (Scheme.ProEt.topology Y) V (𝟙_ Ab.{u + 1})) := by
  refine GrothendieckTopology.flat_presheafToSheaf_obj Ab.{u + 1} _ _ fun W ↦ ?_
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} Ab.{u + 1}
    (ULift.{u + 1} (W.unop ⟶ V))
  exact ObjectProperty.prop_of_iso _
    (Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (W.unop ⟶ V) ↦ 𝟙_ Ab.{u + 1}) Equiv.ulift
      fun _ ↦ Iso.refl _)
    (ObjectProperty.flat_coproduct _ fun _ ↦ ObjectProperty.prop_unit _)

/-- The direct sum `⊕_V ℤ[V]` of the free abelian sheaves on all objects `V` of the small
pro-étale site of `Y`. -/
noncomputable def freeSeparator : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} :=
  ∐ fun (⟨V, _⟩ : Y.ProEt × Unit) ↦ Sheaf.freeYoneda (Scheme.ProEt.topology Y) V (𝟙_ Ab.{u + 1})

lemma isSeparator_freeSeparator : IsSeparator (freeSeparator Y) :=
  Sheaf.isSeparator _ (S := fun _ : Unit ↦ 𝟙_ Ab.{u + 1})
    (by simpa using! AddCommGrpCat.isSeparator_tensorUnit)

lemma flat_freeSeparator : ObjectProperty.flat (freeSeparator Y) :=
  ObjectProperty.flat_coproduct _ fun p ↦ flat_freeYoneda Y p.1

variable {X Y} (f : X ⟶ Y)

/-- The pullback `f^* (⊕_V ℤ[V]) ≅ ⊕_V ℤ[V ×_Y X]`. -/
noncomputable def upperStarFreeSeparatorIso :
    (f)^*[Ab.{u + 1}].obj (freeSeparator Y) ≅
      ∐ fun p : Y.ProEt × Unit ↦ Sheaf.freeYoneda (Scheme.ProEt.topology X)
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj p.1) (𝟙_ Ab.{u + 1}) :=
  haveI := Scheme.ProEt.isContinuous_overPullback f
  PreservesCoproduct.iso _ _ ≪≫ Sigma.mapIso fun p ↦
    Sheaf.freeYonedaPullbackIso _ (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f) p.1 _

lemma flat_upperStar_freeSeparator :
    ObjectProperty.flat ((f)^*[Ab.{u + 1}].obj (freeSeparator Y)) :=
  ObjectProperty.prop_of_iso _ (upperStarFreeSeparatorIso f).symm
    (ObjectProperty.flat_coproduct _ fun _ ↦ flat_freeYoneda X _)

end FreeSeparator

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

instance : PreservesColimitsOfSize.{u + 1, u + 1}
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) :=
  ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).leftAdjoint_preservesColimits

instance : PreservesColimitsOfShape ℤ ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) :=
  ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- **K-flat resolutions preserved by the pullback.** Every complex of `Λ_Y`-modules receives a
quasi-isomorphism from a K-flat complex `Q` whose pullback `mapMod(f^*) Q` is K-flat. -/
theorem exists_quasiIso_kFlat_mapMod_upperStar
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ) :
    ∃ (Q : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ℤ) (π : Q ⟶ K), QuasiIso π ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex
          (.up ℤ)).obj Q) :=
  Functor.exists_quasiIso_kFlat_mapHomologicalComplex_kFlat _
    (Mod.isSeparator_free_obj (isSeparator_freeSeparator Y))
    (Mod.flat_free_obj (flat_freeSeparator Y))
    (ObjectProperty.prop_of_iso _
      (((f)^*[Ab.{u + 1}].mapModFreeFunctorIso (condensedRingObj Λ Y)).app
        (freeSeparator Y)).symm
      (Mod.flat_free_obj (flat_upperStar_freeSeparator f))) K

end AlgebraicGeometry.ProEtale.CondensedRing
