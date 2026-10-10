/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom

/-!
# The lower shriek along a weakly étale morphism

Let `f : V ⟶ U` be a weakly étale morphism, not necessarily a monomorphism, and let
`j_{f!} = ProEtale.localizationLowerShriek A f h` be the lower shriek of
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`: the left Kan extension
along the localization functor `u : V_proét ⥤ U_proét` followed by sheafification, left adjoint
to the pullback `f^*`. This file proves:

- `j_{f!}` is exact. The presheaf-level left Kan extension is pointwise a direct sum over the
  lifts through `f`, hence left exact
  (`AlgebraicGeometry.SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian`),
  and sheafification is exact.
- `j_{f!}` is faithful. The unit `P ⟶ u^* (lan P)` of the presheaf-level left Kan extension is
  a split monomorphism at every object `T`: the colimit computing `(lan P)(u T)` is indexed by
  a category whose objects induce lifts of `u T` through `f`, and the component at the lift
  `T` itself has a retraction which is zero on the other lifts. Since restriction along `u`
  commutes with sheafification, `j_{f!}` followed by restriction is faithful.
- **The projection formula**: the Frobenius map `j_{f!}(f^* K ⊗ M) ⟶ K ⊗ j_{f!} M` is an
  isomorphism, since `f^*` commutes with internal homs
  (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`).
- `f^*` and `j_{f!}` preserve flat sheaves: by the projection formula, tensoring with `f^* F`
  becomes, after the faithful exact functor `j_{f!}`, tensoring with `F`, and tensoring with
  `j_{f!} B` is `j_{f!}` of tensoring with `B` after `f^*`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_localizationLowerShriek`: `j_{f!}` is left
  exact (it is right exact as a left adjoint).
- `AlgebraicGeometry.ProEtale.faithful_localizationLowerShriek`: `j_{f!}` is faithful.
- `AlgebraicGeometry.ProEtale.isIso_frobeniusMap_localizationLowerShriekUpperStarAdjunction`
  and `AlgebraicGeometry.ProEtale.localizationLowerShriekProjectionIso`: the projection
  formula `j_{f!}(f^* K ⊗ M) ≅ K ⊗ j_{f!} M`.
- `AlgebraicGeometry.ProEtale.preservesFlat_upperStar`: `f^*` preserves flat sheaves.
- `AlgebraicGeometry.ProEtale.preservesFlat_localizationLowerShriek`: `j_{f!}` preserves flat
  sheaves.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

/-! ### The unit of the presheaf-level left Kan extension is a split monomorphism -/

namespace SmallSite

variable {A : Type u'} [Category.{u + 1} A] [HasZeroMorphisms A]
  {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative] {V U : Scheme.{u}} {f : V ⟶ U}
  (h : P f)

/-- The cocone over the indexing diagram of the pointwise left Kan extension of
`F : (P.Over ⊤ V)ᵒᵖ ⥤ A` along the localization functor `u` at `u T`, with point `F T`,
whose component at an object `g : u T ⟶ u S` inducing the lift `T ⟶ V` of `u T` through `f`
is `F` applied to the induced morphism `T ⟶ S`, and zero at the objects inducing other
lifts. Its descent is a retraction of the unit `F T ⟶ (lan F)(u T)`. -/
noncomputable def lanRetractionCocone (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) (T : P.Over ⊤ V) :
    Cocone (CostructuredArrow.proj (MorphismProperty.Over.map ⊤ h).op
      (op ((MorphismProperty.Over.map ⊤ h).obj T)) ⋙ F) where
  pt := F.obj (op T)
  ι :=
    { app g := by
        classical
        exact if hg : g.hom.unop.left ≫ g.left.unop.hom = T.hom then
          F.map (MorphismProperty.Over.homMk g.hom.unop.left hg : T ⟶ g.left.unop).op else 0
      naturality g g' m := by
        have hw : g'.hom.unop.left ≫ m.left.unop.left = g.hom.unop.left :=
          congrArg (fun z ↦ z.unop.left) (CostructuredArrow.w m)
        have heq : g.hom.unop.left ≫ g.left.unop.hom = g'.hom.unop.left ≫ g'.left.unop.hom :=
          congrArg Subtype.val (LiftIndex.ofCostructuredArrow_eq_of_hom h m)
        dsimp
        split_ifs with h₁ h₂ h₂
        · rw [Category.comp_id]
          refine (F.map_comp _ _).symm.trans (congrArg F.map ?_)
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact hw
        · exact absurd (heq ▸ h₁) h₂
        · exact absurd (heq ▸ h₂) h₁
        · simp }

variable [∀ F : (P.Over ⊤ V)ᵒᵖ ⥤ A,
  (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F]

/-- The unit `F T ⟶ (lan F)(u T)` of the left Kan extension along the localization functor `u`
has a retraction, the descent of `lanRetractionCocone`. -/
lemma lanUnit_app_app_comp_desc_lanRetractionCocone (F : (P.Over ⊤ V)ᵒᵖ ⥤ A)
    (T : P.Over ⊤ V) :
    ((MorphismProperty.Over.map ⊤ h).op.lanUnit.app F).app (op T) ≫
      ((MorphismProperty.Over.map ⊤ h).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F
        (op ((MorphismProperty.Over.map ⊤ h).obj T))).desc (lanRetractionCocone h F T) =
      𝟙 _ := by
  have := ((MorphismProperty.Over.map ⊤ h).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F
    (op ((MorphismProperty.Over.map ⊤ h).obj T))).fac (lanRetractionCocone h F T)
    (CostructuredArrow.mk (𝟙 _))
  refine Eq.trans ?_ (this.trans ?_)
  · simp [Functor.LeftExtension.coconeAt, Functor.lanUnit]
  · dsimp only [lanRetractionCocone]
    split_ifs with hg
    · refine (congrArg F.map ?_).trans (F.map_id _)
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      rfl
    · exact absurd (Category.id_comp _) hg

/-- The unit `F ⟶ u^* (lan F)` of the left Kan extension along the opposite of the localization
functor `u` of `h : P f` is a monomorphism, for an arbitrary `f`: its components are split
monomorphisms by `lanUnit_app_app_comp_desc_lanRetractionCocone`. -/
instance mono_lanUnit_app_overMap (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    Mono ((MorphismProperty.Over.map ⊤ h).op.lanUnit.app F) := by
  have (T : (P.Over ⊤ V)ᵒᵖ) :
      IsSplitMono (((MorphismProperty.Over.map ⊤ h).op.lanUnit.app F).app T) :=
    IsSplitMono.mk' ⟨_, lanUnit_app_app_comp_desc_lanRetractionCocone h F T.unop⟩
  exact NatTrans.mono_of_mono_app _

end SmallSite

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)

/-! ### Exactness and faithfulness -/

/-- The restriction `j_f^*` along a weakly étale morphism is additive. -/
instance localizationRestriction_additive : (localizationRestriction A f h).Additive where

/-- The lower shriek `j_{f!}` along a weakly étale morphism is additive, being a left
adjoint. -/
instance localizationLowerShriek_additive : (localizationLowerShriek A f h).Additive :=
  (localizationLowerShriekAdjunction A f h).left_adjoint_additive

/-- The lower shriek `j_{f!}` along an arbitrary weakly étale morphism `f` is left exact: it is
the presheaf-level left Kan extension, left exact by
`AlgebraicGeometry.SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian`,
followed by the left exact sheafification. Being a left adjoint, it is also right exact. -/
instance preservesFiniteLimits_localizationLowerShriek :
    PreservesFiniteLimits (localizationLowerShriek A f h) := by
  have : PreservesFiniteLimits (localizationLowerShriekPresheaf A f h) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A h
  rw [localizationLowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

/-- The lower shriek `j_{f!}` along an arbitrary weakly étale morphism `f` is faithful. Its
composite with the restriction `j_f^*` is, since restriction commutes with sheafification
(`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`), the
sheafification of `u^* (lan E)`, which receives the sheafification of the unit
`E ⟶ u^* (lan E)` of the presheaf-level left Kan extension. That unit is a monomorphism by
`AlgebraicGeometry.SmallSite.mono_lanUnit_app_overMap`, and sheafification preserves
monomorphisms and restricts to the identity on sheaves. -/
instance faithful_localizationLowerShriek : (localizationLowerShriek A f h).Faithful := by
  have : (sheafToPresheaf (ProEt.topology V) A ⋙ 𝟭 _ ⋙ presheafToSheaf _ A).Faithful :=
    Functor.Faithful.of_iso (asIso (sheafificationAdjunction (ProEt.topology V) A).counit).symm
  have : (sheafToPresheaf (ProEt.topology V) A ⋙ localizationLowerShriekPresheaf A f h ⋙
      (Functor.whiskeringLeft V.ProEtᵒᵖ U.ProEtᵒᵖ A).obj (MorphismProperty.Over.map ⊤ h).op ⋙
        presheafToSheaf _ A).Faithful :=
    @Functor.Faithful.of_mono_app _ _ _ _ _ _ this (Functor.whiskerLeft (sheafToPresheaf _ A)
      (Functor.whiskerRight (MorphismProperty.Over.map ⊤ h).op.lanUnit (presheafToSheaf _ A)))
      fun _ ↦ (presheafToSheaf _ A).map_mono _
  have : (localizationLowerShriek A f h ⋙ localizationRestriction A f h).Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _ this (Functor.isoWhiskerLeft
      (sheafToPresheaf (ProEt.topology V) A ⋙ localizationLowerShriekPresheaf A f h)
      ((MorphismProperty.Over.map ⊤ h).pushforwardContinuousSheafificationCompatibility A
        (ProEt.topology V) (ProEt.topology U)))
  exact Functor.Faithful.of_comp _ (localizationRestriction A f h)

/-! ### The projection formula -/

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- **The projection formula** for the lower shriek along a weakly étale morphism: the
Frobenius map `j_{f!}(f^* K ⊗ M) ⟶ K ⊗ j_{f!} M` is an isomorphism. This is equivalent to
`f^*` commuting with internal homs, `AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`,
by `CategoryTheory.Adjunction.isIso_frobeniusMap_of_isIso_ihomComparison`. -/
instance isIso_frobeniusMap_localizationLowerShriekUpperStarAdjunction
    (K : Sheaf (ProEt.topology U) A) (M : Sheaf (ProEt.topology V) A) :
    IsIso ((localizationLowerShriekUpperStarAdjunction A f h).frobeniusMap K M) := by
  have := isIso_ihomComparison_upperStar (hg := h) A f K
  exact (localizationLowerShriekUpperStarAdjunction A f
    h).isIso_frobeniusMap_of_isIso_ihomComparison K (fun _ ↦ inferInstance) M

/-- **The projection formula** `j_{f!}(f^* K ⊗ M) ≅ K ⊗ j_{f!} M` for the lower shriek along a
weakly étale morphism `f`, given by the Frobenius map. -/
noncomputable def localizationLowerShriekProjectionIso (K : Sheaf (ProEt.topology U) A)
    (M : Sheaf (ProEt.topology V) A) :
    (localizationLowerShriek A f h).obj ((f)^*[A].obj K ⊗ M) ≅
      K ⊗ (localizationLowerShriek A f h).obj M :=
  asIso ((localizationLowerShriekUpperStarAdjunction A f h).frobeniusMap K M)

/-! ### Preservation of flat sheaves -/

/-- The pullback `f^*` along a weakly étale morphism preserves flat sheaves. For a flat `K`,
tensoring with `f^* K` is right exact and preserves monomorphisms: after the faithful exact
functor `j_{f!}` it becomes, by the projection formula, tensoring with `K` after `j_{f!}`. -/
instance preservesFlat_upperStar [hf : WeaklyEtale f] : (f)^*[A].PreservesFlat where
  flat_obj {K} hK := by
    rw [ObjectProperty.flat_iff_preservesFiniteLimits] at hK ⊢
    have : (tensorLeft ((f)^*[A].obj K)).PreservesMonomorphisms :=
      ⟨fun {M M'} m _ ↦ (localizationLowerShriek A f hf).mono_of_mono_map <| by
        have : Mono (K ◁ (localizationLowerShriek A f hf).map m) := (tensorLeft K).map_mono _
        have : Mono ((localizationLowerShriek A f hf).map ((f)^*[A].obj K ◁ m)) := by
          rw [(IsIso.eq_comp_inv _).2 ((localizationLowerShriekUpperStarAdjunction A f
            hf).map_whiskerLeft_comp_frobeniusMap K m)]
          infer_instance
        exact this⟩
    exact Functor.preservesFiniteLimits_of_preservesMonomorphisms _

/-- The lower shriek `j_{f!}` along a weakly étale morphism preserves flat sheaves. For a flat
`B`, tensoring `j_{f!} B` with `m : C ⟶ C'` is, up to the braiding and the projection formula,
`j_{f!}` of `f^* m ⊗ B`, which is a monomorphism if `m` is: `f^*`, tensoring with `B` and
`j_{f!}` all preserve monomorphisms. -/
instance preservesFlat_localizationLowerShriek :
    (localizationLowerShriek A f h).PreservesFlat where
  flat_obj {B} hB := by
    have : PreservesFiniteLimits (tensorRight B) := ((exactFunctor_iff _).1 hB.2).1
    have : (f)^*[A].IsRightAdjoint :=
      (localizationLowerShriekUpperStarAdjunction A f h).isRightAdjoint
    rw [ObjectProperty.flat_iff_preservesFiniteLimits]
    have : (tensorLeft ((localizationLowerShriek A f h).obj B)).PreservesMonomorphisms :=
      ⟨fun {C C'} m _ ↦ by
        have : Mono ((f)^*[A].map m) := (f)^*[A].map_mono m
        have : Mono ((f)^*[A].map m ▷ B) := (tensorRight B).map_mono ((f)^*[A].map m)
        have : Mono (m ▷ (localizationLowerShriek A f h).obj B) := by
          rw [← (IsIso.inv_comp_eq _).2 ((localizationLowerShriekUpperStarAdjunction A f
            h).map_whiskerRight_comp_frobeniusMap m B)]
          infer_instance
        have : Mono ((localizationLowerShriek A f h).obj B ◁ m ≫ (β_ _ _).hom) := by
          rw [BraidedCategory.braiding_naturality_right]
          infer_instance
        exact mono_of_mono ((localizationLowerShriek A f h).obj B ◁ m) (β_ _ _).hom⟩
    exact Functor.preservesFiniteLimits_of_preservesMonomorphisms _

end ProEtale

end AlgebraicGeometry
