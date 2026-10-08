/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

/-!
# Restriction of internal homs of pro-étale sheaves

Let `g : W ⟶ V` be weakly étale. The pullback `g^*` of sheaves of modules on the small
pro-étale sites is restriction along the localization functor `W.ProEt ⥤ V.ProEt`
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and it commutes with
internal homs: `g^* [F, G] ≅ [g^* F, g^* G]`
(`AlgebraicGeometry.ProEtale.upperStarIhomIsoOfWeaklyEtale`).

The underlying presheaf of `[F, G]` is the internal hom of presheaves, whose sections over `U`
are the morphisms between the restrictions of `F` and `G` to the slice over `U`
(`CategoryTheory.GrothendieckTopology.sheafToPresheafIhomIso`). The localization functor
induces equivalences of these slices, `W.ProEt / T ≌ V.ProEt / T`, so internal homs of
presheaves commute with restriction along it (`ModuleCat.functorEnrichedHomCompIso`).

## Main definitions

- `AlgebraicGeometry.ProEtale.localizationRestrictionIhomIso`: `j^* [F, G] ≅ [j^* F, j^* G]`
  for the restriction `j^*` along a weakly étale morphism.
- `AlgebraicGeometry.ProEtale.upperStarIhomIsoOfWeaklyEtale`: `g^* [F, G] ≅ [g^* F, g^* G]` for
  a weakly étale `g`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace CategoryTheory

variable {T : Type*} [Category T] {P : MorphismProperty T} {X Y : T}

section Post

variable [P.IsStableUnderComposition] [P.HasOfPostcompProperty P] {f : X ⟶ Y} (hPf : P f)
  (T : (P.Over ⊤ X)ᵒᵖ)

/-- The functor `MorphismProperty.Over.map` induces a full functor
`Under T ⥤ Under (op (map T.unop))` on the opposite slices: a morphism `B' ⟶ A'` over `map T`
is a morphism over `T`, since `A' ⟶ X` factors through `T`. -/
instance MorphismProperty.Over.full_post_op_map :
    (Under.post (X := T) (MorphismProperty.Over.map ⊤ hPf).op).Full where
  map_surjective {A B} φ := by
    have hw : φ.right.unop.left ≫ A.hom.unop.left = B.hom.unop.left :=
      congrArg (fun g ↦ g.unop.left) (CategoryTheory.Under.w φ)
    refine ⟨CategoryTheory.Under.homMk (MorphismProperty.Over.homMk (A := B.right.unop)
      (B := A.right.unop) φ.right.unop.left ?_ trivial).op ?_, ?_⟩
    · rw [← MorphismProperty.Over.w A.hom.unop, reassoc_of% hw, MorphismProperty.Over.w B.hom.unop]
    · apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      exact hw
    · ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      simp

/-- The functor `MorphismProperty.Over.map` induces an essentially surjective functor
`Under T ⥤ Under (op (map T.unop))` on the opposite slices: an object `B ⟶ map T` is the image
of `B ⟶ T`, the structure morphism `B ⟶ X` satisfying `P` by cancellation. -/
instance MorphismProperty.Over.essSurj_post_op_map :
    (Under.post (X := T) (MorphismProperty.Over.map ⊤ hPf).op).EssSurj where
  mem_essImage B := by
    have hB : B.hom.unop.left ≫ T.unop.hom ≫ f = B.right.unop.hom := by
      simpa using MorphismProperty.Over.w B.hom.unop
    have hP : P (B.hom.unop.left ≫ T.unop.hom) := P.comp_mem _ _
      (P.of_postcomp _ (T.unop.hom ≫ f) (P.comp_mem _ _ T.unop.prop hPf)
        (hB ▸ B.right.unop.prop)) T.unop.prop
    let S : P.Over ⊤ X := MorphismProperty.Over.mk ⊤ (B.hom.unop.left ≫ T.unop.hom) hP
    let a : S ⟶ T.unop := MorphismProperty.Over.homMk B.hom.unop.left rfl trivial
    refine ⟨CategoryTheory.Under.mk a.op, ⟨CategoryTheory.Under.isoMk
      (MorphismProperty.Over.isoMk (A := B.right.unop)
        (B := (MorphismProperty.Over.map ⊤ hPf).obj S) (Iso.refl B.right.unop.left)
        (by simp [S, hB])).op ?_⟩⟩
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    simp only [a]
    exact Category.id_comp _

/-- The functor `MorphismProperty.Over.map` induces equivalences
`Under T ≌ Under (op (map T.unop))` of opposite slices. -/
instance MorphismProperty.Over.isEquivalence_post_op_map :
    (Under.post (X := T) (MorphismProperty.Over.map ⊤ hPf).op).IsEquivalence where

end Post

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open GrothendieckTopology

variable {R : Type (u + 1)} [CommRing R] {V W : Scheme.{u}}

/-- The localization functor `W.ProEt ⥤ V.ProEt` along a weakly étale `g` induces equivalences
of the opposite slices `W.ProEt / T ≌ V.ProEt / T`. -/
instance isEquivalence_post_op_overMap (g : W ⟶ V) (h : WeaklyEtale g) (d : W.ProEtᵒᵖ) :
    (Under.post (X := d) (MorphismProperty.Over.map ⊤ h).op).IsEquivalence :=
  MorphismProperty.Over.isEquivalence_post_op_map (P := @WeaklyEtale) h d

/-- The restriction `j^*` of sheaves of modules along a weakly étale `g : W ⟶ V` commutes with
internal homs: on underlying presheaves both sides are internal homs of presheaves, and the
localization functor induces equivalences of slices. -/
noncomputable def localizationRestrictionIhomIso (g : W ⟶ V) (h : WeaklyEtale g)
    (F G : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} R)) :
    (localizationRestriction _ g h).obj ((ihom F).obj G) ≅
      (ihom ((localizationRestriction _ g h).obj F)).obj
        ((localizationRestriction _ g h).obj G) :=
  let u := MorphismProperty.Over.map ⊤ h
  let e₁ : u.op ⋙ ((ihom F).obj G).obj ≅
      u.op ⋙ functorEnrichedHom (ModuleCat.{u + 1} R) F.obj G.obj :=
    Functor.isoWhiskerLeft u.op (sheafToPresheafIhomIso _ F G)
  let e₂ : u.op ⋙ functorEnrichedHom (ModuleCat.{u + 1} R) F.obj G.obj ≅
      functorEnrichedHom (ModuleCat.{u + 1} R) (u.op ⋙ F.obj) (u.op ⋙ G.obj) :=
    ModuleCat.functorEnrichedHomCompIso u F.obj G.obj
  let e₃ : functorEnrichedHom (ModuleCat.{u + 1} R) ((localizationRestriction _ g h).obj F).obj
      ((localizationRestriction _ g h).obj G).obj ≅
      ((ihom ((localizationRestriction _ g h).obj F)).obj
        ((localizationRestriction _ g h).obj G)).obj :=
    (sheafToPresheafIhomIso _ _ _).symm
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (e₁ ≪≫ e₂ ≪≫ e₃)

/-- The pullback `g^*` of sheaves of modules along a weakly étale `g` commutes with internal
homs, `g^*` being restriction along the localization functor. -/
noncomputable def upperStarIhomIsoOfWeaklyEtale (g : W ⟶ V) [h : WeaklyEtale g]
    (F G : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} R)) :
    (g)^*[ModuleCat.{u + 1} R].obj ((ihom F).obj G) ≅
      (ihom ((g)^*[ModuleCat.{u + 1} R].obj F)).obj ((g)^*[ModuleCat.{u + 1} R].obj G) :=
  (upperStarIsoLocalizationRestriction _ g h).app _ ≪≫ localizationRestrictionIhomIso g h F G ≪≫
    (ihom _).mapIso ((upperStarIsoLocalizationRestriction _ g h).app G).symm ≪≫
    (MonoidalClosed.internalHom.mapIso
      ((upperStarIsoLocalizationRestriction _ g h).app F).op).app _

end AlgebraicGeometry.ProEtale
