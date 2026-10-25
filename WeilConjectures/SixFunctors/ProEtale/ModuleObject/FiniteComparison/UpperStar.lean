/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafModuleIsoOfForget
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# The comparison of the two finite-coefficient models commutes with pullback

Let `T` be a finite discrete commutative ring and `f : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` between module objects over the condensed
coefficient ring `T̲_X = p_X^* C(-, T)` and pro-étale sheaves of `T`-modules commutes with the
pushforwards (`ProEtale.lowerStarFiniteCoefficientModEquivalenceIso`): the pushforward of module
objects has underlying abelian sheaf `f_* M`, with `T̲_Y` acting through `η_f : T̲_Y ⟶ f_* T̲_X`,
the pushforward of sheaves of `T`-modules has the same underlying abelian sheaf, and the actions
of `t ∈ T` agree, being the actions of the constant global section `t`
(`ProEtale.finiteCoefficientModEquivalence_smul`), which `η_f` sends to the pushforward of the
constant global section `t` (`ProEtale.ε_comp_map_comp_condensedPushforwardHom`). By uniqueness
of left adjoints it commutes with the pullbacks
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal
  Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (G : C ⥤ D) [G.LaxMonoidal] {A : C} [MonObj A]

/-- A lax monoidal functor `G` sends the action of a global section `σ` of `A` on an
`A`-module object `M` to the action of the global section `ε ≫ G σ` of `G A` on `G M`. -/
lemma globalSmul_mapMod_obj (σ : 𝟙_ C ⟶ A) (M : Mod C A) :
    Mod.globalSmul (ε G ≫ G.map σ) ((G.mapMod A).obj M) = G.map (Mod.globalSmul σ M) := by
  rw [Mod.globalSmul, Mod.globalSmul, G.map_comp, G.map_comp, ← left_unitality_inv_assoc,
    ← μ_natural_left_assoc, comp_whiskerRight, Category.assoc]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

section GlobalSections

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] {X Y : Scheme.{u}}
  (f : X ⟶ Y)

omit [MonObj Λ] in
/-- `η_f : Λ_Y ⟶ f_* Λ_X` sends the image `ε ≫ p_Y^* s` of a global section `s` of `Λ` to the
pushforward of its image `ε ≫ p_X^* s`. -/
lemma ε_comp_map_comp_condensedPushforwardHom (s : 𝟙_ _ ⟶ Λ) :
    ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s ≫ condensedPushforwardHom Λ f =
      ε (f)_*[Ab.{u + 1}] ≫
        (f)_*[Ab.{u + 1}].map (ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s) := by
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  have hε : ε (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]) =
      ε (f)^*[Ab.{u + 1}] ≫ (f)^*[Ab.{u + 1}].map (ε (upperStarFromPoint Y)) := rfl
  rw [← unitAlgHom_comp_map_condensedPullbackHom,
    ← NatTrans.IsMonoidal.ε_comp_map_comp_app (upperStarFromPointComp f).hom s, hε,
    ← adj.unit_app_unit_comp_map_η, Category.assoc, ← Functor.map_comp, Category.assoc,
    Functor.Monoidal.η_ε_assoc, Functor.comp_map, Functor.map_comp, Functor.map_comp,
    adj.unit_naturality_assoc, adj.unit_naturality_assoc]

/-- The action of the image `ε ≫ p_Y^* s` of a global section `s` of `Λ` on the pushforward
`f_* M` is the pushforward of the action of `ε ≫ p_X^* s` on `M`. -/
lemma globalSmul_lowerStar_obj (s : 𝟙_ _ ⟶ Λ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.globalSmul (ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s)
        ((f)_*⟦Λ⟧.obj M) =
      (f)_*[Ab.{u + 1}].map
        (Mod.globalSmul (ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s) M) := by
  refine (Mod.globalSmul_comap (condensedPushforwardHom Λ f) _
    (((f)_*[Ab.{u + 1}].mapMod _).obj M)).trans ?_
  rw [Category.assoc, ε_comp_map_comp_condensedPushforwardHom, Functor.globalSmul_mapMod_obj]

end GlobalSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T]

/-- The action of `t ∈ T` on the sections over `U` of the pushforward of the sheaf of
`T`-modules corresponding to `M` is the action on `M` of the constant global section `t` of
`Λ_X`, over the base change of `U`. -/
lemma lowerStar_finiteCoefficientModEquivalence_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (U : Y.ProEtᵒᵖ) (t : T)
    (y : ((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
      ((finiteCoefficientModEquivalence X T).functor.obj M)).obj.obj U) :
    (ULift.up t : ULift.{u + 1} T) • y =
      (Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom) M).hom.app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop)) y :=
  finiteCoefficientModEquivalence_smul X T M _ t y

/-- The pushforward commutes with `finiteCoefficientModEquivalence` on a single module object
`M`: the identity of the underlying abelian sheaf `f_* M` is `T`-linear. -/
noncomputable def lowerStarFiniteCoefficientModEquivalenceObjIso
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (finiteCoefficientModEquivalence Y T).functor.obj
        ((f)_*⟦Profinite.continuousMapRingObj T⟧.obj M) ≅
      (f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        ((finiteCoefficientModEquivalence X T).functor.obj M) :=
  Sheaf.isoOfForget₂Iso (Iso.refl _) fun U t x ↦ by
    obtain ⟨t⟩ := t
    rw [finiteCoefficientModEquivalence_smul Y T
        ((f)_*⟦Profinite.continuousMapRingObj T⟧.obj M) U t x,
      lowerStar_finiteCoefficientModEquivalence_smul, globalSmul_lowerStar_obj]
    rfl

/-- **The pushforward commutes with `finiteCoefficientModEquivalence`**: the pushforward of
module objects over `T̲` corresponds to the pushforward of sheaves of `T`-modules. Both have
underlying abelian sheaf `f_* M`; the actions of `t ∈ T` agree since `η_f` sends the constant
section `t` of `Λ_Y` to the pushforward of the constant section `t` of `Λ_X`. -/
noncomputable def lowerStarFiniteCoefficientModEquivalenceIso :
    (f)_*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence Y T).functor ≅
      (finiteCoefficientModEquivalence X T).functor ⋙
        (f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  NatIso.ofComponents (lowerStarFiniteCoefficientModEquivalenceObjIso f T) fun {M N} φ ↦ by
    ext U x
    rfl

/-- The pushforward of sheaves of `T`-modules is the pushforward of module objects over `T̲`,
conjugated by `finiteCoefficientModEquivalence`. -/
noncomputable def finiteCoefficientModEquivalenceInverseLowerStarIso :
    (finiteCoefficientModEquivalence X T).inverse ⋙
        ((f)_*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence Y T).functor) ≅
      (f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  Functor.isoWhiskerLeft _ (lowerStarFiniteCoefficientModEquivalenceIso f T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientModEquivalence X T).counitIso _ ≪≫
    Functor.leftUnitor _

/-- The pullback of module objects over `T̲`, conjugated by `finiteCoefficientModEquivalence`, is
left adjoint to the pushforward of sheaves of `T`-modules. -/
noncomputable def finiteCoefficientModEquivalenceUpperStarLowerStarAdjunction :
    ((finiteCoefficientModEquivalence Y T).inverse ⋙ (f)^*⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientModEquivalence X T).functor ⊣
      (f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (((finiteCoefficientModEquivalence Y T).symm.toAdjunction.comp
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)).comp
      (finiteCoefficientModEquivalence X T).toAdjunction).ofNatIsoRight
    (finiteCoefficientModEquivalenceInverseLowerStarIso f T)

/-- **The pullback commutes with `finiteCoefficientModEquivalence`**: the pullback of module
objects over `T̲` corresponds to the pullback of sheaves of `T`-modules. Both are left adjoint
to the pushforwards, which correspond by `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def upperStarFiniteCoefficientModEquivalenceIso :
    (f)^*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence X T).functor ≅
      (finiteCoefficientModEquivalence Y T).functor ⋙
        (f)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientModEquivalence Y T).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      (finiteCoefficientModEquivalenceUpperStarLowerStarAdjunction f T).leftAdjointUniq
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f))

end AlgebraicGeometry.ProEtale
