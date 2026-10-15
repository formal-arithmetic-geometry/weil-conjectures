/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Free sheaves under extension by zero and pullback, and cohomology

For an étale `v : V ⟶ Y`, extension by zero sends the free sheaf `Λ[T]` on an étale
`V`-scheme `T` to the free sheaf on `T → V → Y`, and the derived adjunction `v_! ⊣ v^*`
identifies `Hom((v_! M)[0], N[0]⟦q⟧)` with `Hom(M[0], (v^* N)[0]⟦q⟧)`. Combined with
`h^* Λ[W] ≅ Λ[W ×_X Y]`, this computes `Hom((h^* Λ[W])[0], N[0]⟦q⟧)` as the étale cohomology
`Hᵠ(W ×_X Y, N|)` of the scheme `W ×_X Y`. The file also states that étale cohomology of a
quasi-compact quasi-separated scheme commutes with filtered colimits.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriekFreeSheafIso`: `v_! Λ[T] ≅ Λ[T → V → Y]`.
- `AlgebraicGeometry.Etale.shiftedHomFunctor`: the functor `N ↦ Hom(A[0], N[0]⟦q⟧)`.
- `AlgebraicGeometry.Etale.etaleLowerShriekShiftedHomIso`: the derived adjunction `v_! ⊣ v^*`
  on shifted maps out of a sheaf in degree `0`.
- `AlgebraicGeometry.Etale.shiftedHomFunctorUpperStarFreeSheafIso`:
  `Hom((h^* Λ[W])[0], N[0]⟦q⟧) ≅ Hᵠ(W ×_X Y, N|)`.

## Main statements

- `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`:
  étale cohomology of a quasi-compact quasi-separated scheme commutes with filtered colimits.
-/

@[expose] public section

universe u w

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FreeSheaf

variable {X Y : Scheme.{u}}

/-- Maps out of `v_! Λ[T]` are maps out of `Λ[T → V → Y]`, for `v : V ⟶ Y` étale. -/
noncomputable def Etale.etaleLowerShriekFreeSheafHomEquiv {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ⟶
      G) ≃ ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) ⟶ G) :=
  (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).homEquiv _ _).trans
    (((Iso.refl _).homCongr
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) v hv).app G)).trans
    (Etale.freeSheafHomEquiv Λ T _))).trans (Etale.freeSheafHomEquiv Λ _ G).symm

lemma Etale.etaleLowerShriekFreeSheafHomEquiv_comp {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj
      ((Etale.freeSheaf Λ V).obj T) ⟶ G) (g : G ⟶ G') :
    Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G' (f ≫ g) =
      Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G f ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.etaleLowerShriekFreeSheafHomEquiv, Equiv.trans_apply,
    Etale.freeSheafHomEquiv_comp, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Adjunction.homEquiv_naturality_right, Category.assoc, Iso.app_hom,
    NatTrans.naturality]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Extension by zero of a free sheaf along an étale morphism `v : V ⟶ Y` is free:
`v_! Λ[T] ≅ Λ[T → V → Y]`, both corepresenting the functor `G ↦ G(T → V → Y)`. -/
noncomputable def Etale.etaleLowerShriekFreeSheafIso {V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)
    (T : V.Etale) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun G ↦ (Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G).toIso)
    (fun g ↦ by
      ext f
      exact Etale.etaleLowerShriekFreeSheafHomEquiv_comp Λ v hv T f g))).unop.symm

end FreeSheaf

section Restriction

variable {Y V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)

instance Etale.additive_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).Additive :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).left_adjoint_additive

instance Etale.isLeftAdjoint_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).IsLeftAdjoint :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).isLeftAdjoint

/-- The derived adjunction `v_! ⊣ v^*` on bounded below derived categories, for an étale `v`:
both functors are exact. -/
noncomputable def Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlus ⊣
      ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  ((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).derivedPlus).ofNatIsoRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _)

/-- The functor `N ↦ Hom(A[0], N[0]⟦q⟧)` on sheaves of `Λ`-modules on `Z_ét`; for `A = Λ` it is
the étale cohomology `N ↦ Hᵠ(Z, N)` with coefficients in `Λ`-modules. -/
noncomputable abbrev Etale.shiftedHomFunctor {Z : Scheme.{u}}
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj A))

/-- An exact functor commutes with degree-zero single objects and shifts.
This is the composition of its single-object and shift comparison isomorphisms. -/
noncomputable def Etale.exactSingleShiftIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (q : ℤ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ shiftFunctor _ q ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D 0 ⋙ shiftFunctor _ q :=
  Functor.isoWhiskerLeft _ (F.mapDerivedCategoryPlus.commShiftIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategoryPlusSingleFunctor 0) (shiftFunctor _ q) ≪≫
    Functor.associator _ _ _

/-- A named copy of pullback used to share its derived-shift comparison instances. -/
noncomputable def Etale.upperStarForShift :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (v)^*[ModuleCat.{u + 1} Λ]

instance Etale.additive_upperStarForShift : (Etale.upperStarForShift Λ v).Additive := by
  dsimp [Etale.upperStarForShift]
  infer_instance

/-- Pullback, in its named presentation, preserves finite limits. -/
theorem Etale.preservesFiniteLimits_upperStarForShift :
    PreservesFiniteLimits (Etale.upperStarForShift Λ v) := by
  dsimp [Etale.upperStarForShift]
  infer_instance

instance Etale.preservesFiniteColimits_upperStarForShift :
    PreservesFiniteColimits (Etale.upperStarForShift Λ v) := by
  dsimp [Etale.upperStarForShift]
  infer_instance

/-- `v^*` commutes with `N ↦ N[0]⟦q⟧`. -/
noncomputable def Etale.upperStarSingleShiftIso (q : ℤ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q := by
  letI := Etale.preservesFiniteLimits_upperStarForShift Λ v
  exact Etale.exactSingleShiftIso (Etale.upperStarForShift Λ v) q

/-- Transport the additive Hom equivalence of an adjunction across two isomorphisms. -/
noncomputable def Etale.adjunctionHomAddEquivOfIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {N A : D} {B : C} (i₁ : L.obj M ≅ A) (i₂ : R.obj N ≅ B) :
    (A ⟶ N) ≃+ (M ⟶ B) :=
  AddEquiv.mk'
    { toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
      invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
      left_inv f := by simp
      right_inv g := by simp }
    (fun f g ↦ by simp)

lemma Etale.adjunctionHomAddEquivOfIso_apply
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {N A : D} {B : C} (i₁ : L.obj M ≅ A) (i₂ : R.obj N ≅ B) (f : A ⟶ N) :
    Etale.adjunctionHomAddEquivOfIso adj i₁ i₂ f =
      adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom := rfl

/-- The transported additive Hom equivalence is natural in its target argument. -/
noncomputable def Etale.adjunctionHomNatIso
    {C D E : Type*} [Category.{w} C] [Category.{w} D] [Category E]
    [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {A : D} (i₁ : L.obj M ≅ A) (S : E ⥤ D) (T : E ⥤ C)
    (e : S ⋙ R ≅ T) :
    S ⋙ preadditiveCoyoneda.obj (op A) ≅ T ⋙ preadditiveCoyoneda.obj (op M) :=
  NatIso.ofComponents
    (fun N ↦ (Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N)).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N') (f ≫ S.map g) =
        Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N) f ≫ T.map g
      rw [Etale.adjunctionHomAddEquivOfIso_apply, Etale.adjunctionHomAddEquivOfIso_apply,
        ← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
      congr 1
      exact e.hom.naturality g)

/-- The derived adjunction `v_! ⊣ v^*` on shifted maps out of a sheaf placed in degree `0`,
naturally in the target. -/
noncomputable def Etale.etaleLowerShriekShiftedHomIso
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ Etale.shiftedHomFunctor Λ M q :=
  let adj := Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv
  let i₁ := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
    0).app M
  let S := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙ shiftFunctor _ q
  let T := (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙ shiftFunctor _ q
  let e := Functor.associator _ _ _ ≪≫ Etale.upperStarSingleShiftIso Λ v hv q
  (Functor.associator _ _ _).symm ≪≫ Etale.adjunctionHomNatIso adj i₁ S T e ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((v)^*[ModuleCat.{u + 1} Λ]) (Functor.associator _ _ _)

end Restriction

/-- The final object of the small étale site of `Z`, the identity of `Z`. -/
noncomputable abbrev Etale.finalObject (Z : Scheme.{u}) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))

/-- Blueprint `lem-weil-pbc-cohomology-filtered-colimit` (subsection `sk-prop-h2`): Filtered
colimits of étale cohomology. Let `Z` be a quasi-compact and quasi-separated scheme. Then étale
cohomology `N ↦ Hᵠ(Z, N) = Hom(Λ_Z[0], N[0]⟦q⟧)` with coefficients in sheaves of `Λ`-modules
commutes with filtered colimits: `colim Hᵠ(Z, N_a) ≅ Hᵠ(Z, colim N_a)`.

The same statement for abelian sheaves is
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. -/
@[stacks 03Q6]
theorem Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type u) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) := by
  classical
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let R := DerivedCategory.singleFunctor
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} Λ) Z (n : ℤ)
    have : PreservesColimitsOfShape J R :=
      ⟨fun {D} ↦ preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
        (Scheme.etaleModuleCohomology_isColimit_of_isFiltered Z Λ
          (colimit.isColimit D) n).some⟩
    let e := (Scheme.nonempty_freeSheafDerivedSectionsIso Z Λ n).some
    have : PreservesColimitsOfShape J
        (R ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := inferInstance
    exact preservesColimitsOfShape_of_natIso
      (Functor.associator
        (DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
        (Etale.cohomology (ModuleCat.{u + 1} Λ) Z (n : ℤ))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≪≫ e.symm)
  · have hq : q < 0 := lt_of_not_ge hq
    let F := Etale.shiftedHomFunctor Λ
      ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q
    apply F.preservesColimitsOfShape_of_isZero _ J
    rw [Functor.isZero_iff]
    intro N
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    change Subsingleton
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) ⟶
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)⟦q⟧)
    refine ⟨fun f g ↦ ?_⟩
    have hz (f : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) ⟶
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)⟦q⟧) : f = 0 := by
      let t := DerivedCategory.Plus.TStructure.t
        (C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      have ht := t.isGE_shift ((DerivedCategory.Plus.singleFunctor _ 0).obj N)
        0 q (-q) (by omega)
      exact t.zero f 0 (-q) (by omega)
    exact (hz f).trans (hz g).symm

/-- An isomorphism `A ≅ A'` identifies the functors `N ↦ Hom(A[0], N[0]⟦q⟧)` and
`N ↦ Hom(A'[0], N[0]⟦q⟧)`. -/
noncomputable def Etale.shiftedHomFunctorMapIso {Z : Scheme.{u}}
    {A A' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : A ≅ A') (q : ℤ) :
    Etale.shiftedHomFunctor Λ A q ≅ Etale.shiftedHomFunctor Λ A' q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q)
    (preadditiveCoyoneda.mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e).symm.op)

section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- An étale `Y`-scheme `W`, as an étale scheme over itself extended along its structure
morphism, is `W`. -/
noncomputable def Etale.overMapFinalObjectIso (W : Y.Etale) :
    (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.finalObject W.left) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

/-- The functor `N ↦ Hom((h^* Λ[W])[0], N[0]⟦q⟧)` is the cohomology functor of `W ×_X Y`
precomposed with restriction. -/
noncomputable def Etale.shiftedHomFunctorUpperStarFreeSheafIso (W : X.Etale) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q ≅
      (((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.shiftedHomFunctor Λ
          ((Etale.freeSheaf Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj
            (Etale.finalObject _)) q :=
  Etale.shiftedHomFunctorMapIso Λ (Etale.upperStarFreeSheafIso Λ h W ≪≫
    (Etale.freeSheaf Λ Y).mapIso (Etale.overMapFinalObjectIso _).symm ≪≫
    (Etale.etaleLowerShriekFreeSheafIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
      (Etale.finalObject _)).symm) q ≪≫
  Etale.etaleLowerShriekShiftedHomIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
    _ q

end Pullback

end AlgebraicGeometry
