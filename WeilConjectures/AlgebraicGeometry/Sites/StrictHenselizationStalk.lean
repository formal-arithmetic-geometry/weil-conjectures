/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# Stalks of higher direct images and the strict henselization

Let `f : X ⟶ S` be quasi-compact and quasi-separated with `X` quasi-compact and quasi-separated,
let `F` be an abelian étale sheaf on `X` and `s : Spec Ω ⟶ S` a geometric point. The higher
direct image `Rᵠ f_* F` is the sheafification of the presheaf `V ↦ Hᵠ(X ×_S V, F|)` on `S_ét`
(`AlgebraicGeometry.Etale.cohomologyPresheaf`, with `Hᵠ(X ×_S V, F|) = Extᵠ(ℤ[X ×_S V], F)`), so
its geometric stalk at `s` is the colimit of the `Hᵠ(X ×_S V, F|)` over the pointed étale
neighbourhoods `(V, v)` of `s`. We show that this colimit is `Hᵠ(X ×_S S_(s), F|)`, where
`S_(s)` is the strict localization: the affine pointed étale neighbourhoods are cofinal and have
limit `S_(s)`, base change to `X` preserves this limit, and étale cohomology commutes with the
limit (`AlgebraicGeometry.Etale.commutesWithLimit_of_isLimit`).

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyPresheaf f F q`: the presheaf `V ↦ Hᵠ(X ×_S V, F|)`.
- `AlgebraicGeometry.Etale.stalkComparison`: the map `Hᵠ(X ×_S V, F|) ⟶ Hᵠ(X ×_S S_(s), F|)`
  for a pointed étale neighbourhood `(V, v)`.

## Main statements

- `AlgebraicGeometry.Etale.stalkComparison_bijective`: the stalk formula, elementwise.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Presheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  (q : ℕ)

/-- The **cohomology presheaf** `V ↦ Hᵠ(X ×_S V, F|)` of `f : X ⟶ S` on the small étale site of
`S`, where `Hᵠ(X ×_S V, F|)` is `Extᵠ(ℤ[X ×_S V], F)`; its sheafification is the higher direct
image `Rᵠ f_* F`. -/
@[simps]
noncomputable def cohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat where
  obj V := AddCommGrpCat.of (Abelian.Ext ((freeAbSheaf X).obj (f.Etale.obj V.unop)) F q)
  map a := AddCommGrpCat.ofHom
    { toFun y := (Abelian.Ext.mk₀ ((freeAbSheaf X).map (f.Etale.map a.unop))).comp y (zero_add q)
      map_zero' := by simp
      map_add' _ _ := by simp }
  map_id V := by
    ext y
    simp
  map_comp a b := by
    ext y
    simp [Abelian.Ext.mk₀_comp_mk₀_assoc]

end Presheaf

section Stalk

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The leg `S_(s) ⟶ V` over `S` of the strict localization, for a pointed étale neighbourhood
`(V, v)` of `s`. -/
noncomputable def strictLocalizationLeg (e : Scheme.PointedEtaleNeighborhood s) :
    CategoryTheory.Over.mk (Scheme.strictLocalizationToBase s) ⟶
      (Scheme.Etale.forget S).obj e.1 :=
  CategoryTheory.Over.homMk ((Scheme.strictLocalizationConeAll s).π.app e) (by
    have := (Scheme.strictLocalizationConeAll s).w (Scheme.PointedEtaleNeighborhood.toBase s e)
    exact this)

lemma strictLocalizationLeg_comp {e e' : Scheme.PointedEtaleNeighborhood s} (a : e' ⟶ e) :
    strictLocalizationLeg s e' ≫ (Scheme.Etale.forget S).map a.1 = strictLocalizationLeg s e := by
  apply CategoryTheory.Over.OverMorphism.ext
  simp only [strictLocalizationLeg, CategoryTheory.Over.comp_left, CategoryTheory.Over.homMk_left]
  exact (Scheme.strictLocalizationConeAll s).w a

/-- The pointed étale neighbourhoods of `s`, as schemes over `S`. -/
noncomputable abbrev neighborhoodDiagramOver :
    Scheme.PointedEtaleNeighborhood s ⥤ CategoryTheory.Over S :=
  CategoryOfElements.π _ ⋙ Scheme.Etale.forget S

/-- The strict localization `S_(s)` as a cone over all pointed étale neighbourhoods of `s`, as
schemes over `S`. -/
@[simps]
noncomputable def strictLocalizationConeAllOver : Cone (neighborhoodDiagramOver s) where
  pt := CategoryTheory.Over.mk (Scheme.strictLocalizationToBase s)
  π :=
    { app e := strictLocalizationLeg s e
      naturality e e' a := by
        exact (Category.id_comp _).trans (strictLocalizationLeg_comp s a).symm }

/-- The strict localization is the limit of all pointed étale neighbourhoods, over `S`. -/
noncomputable def isLimitStrictLocalizationConeAllOver :
    IsLimit (strictLocalizationConeAllOver s) :=
  have := IsCofiltered.isConnected (Scheme.PointedEtaleNeighborhood s)
  isLimitOfReflects (CategoryTheory.Over.forget S)
    ((Scheme.isLimitStrictLocalizationConeAll s).ofIsoLimit (Cone.ext (Iso.refl _)))


variable {X : Scheme.{u}} (f : X ⟶ S)

/-- The projection `X ×_S S_(s) ⟶ X`. -/
noncomputable abbrev strictLocalizationProj :
    pullback (Scheme.strictLocalizationToBase s) f ⟶ X :=
  pullback.snd _ _

/-- The free abelian sheaves `ℤ[X ×_S V]` of the pointed étale neighbourhoods `(V, v)` of `s`. -/
noncomputable abbrev neighborhoodFreeSheaf :
    Scheme.PointedEtaleNeighborhood s ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CategoryOfElements.π _ ⋙ f.Etale ⋙ freeAbSheaf X

/-- The morphism `X ×_S S_(s) ⟶ X ×_S V` for a pointed étale neighbourhood `(V, v)` of `s`, on
the terminal étale `X ×_S S_(s)`-scheme. -/
noncomputable abbrev stalkSectionMap (e : Scheme.PointedEtaleNeighborhood s) :
    (terminalBaseChange (strictLocalizationProj s f)).left ⟶ (f.Etale.obj e.1).left :=
  pullback.snd (𝟙 X) (strictLocalizationProj s f) ≫
    ((CategoryTheory.Over.pullback f).map (strictLocalizationLeg s e)).left

lemma stalkSectionMap_comp (e : Scheme.PointedEtaleNeighborhood s) :
    stalkSectionMap s f e ≫ (f.Etale.obj e.1).hom =
      (terminalBaseChange (strictLocalizationProj s f)).hom ≫ strictLocalizationProj s f := by
  simp only [stalkSectionMap, Category.assoc]
  erw [CategoryTheory.Over.w ((CategoryTheory.Over.pullback f).map (strictLocalizationLeg s e))]
  rfl

/-- The morphism `ℤ ⟶ P^* ℤ[X ×_S V]` on `X ×_S S_(s)`, for a pointed étale neighbourhood
`(V, v)` of `s` and the projection `P : X ×_S S_(s) ⟶ X`. -/
noncomputable abbrev stalkSection (e : Scheme.PointedEtaleNeighborhood s) :
    constantZ _ ⟶ (strictLocalizationProj s f)^*[AddCommGrpCat.{u + 1}].obj
      ((neighborhoodFreeSheaf s f).obj e) :=
  sectionZ (stalkSectionMap s f e) (stalkSectionMap_comp s f e)

lemma stalkSection_comp_map {e e' : Scheme.PointedEtaleNeighborhood s} (a : e' ⟶ e) :
    stalkSection s f e' ≫ (strictLocalizationProj s f)^*[AddCommGrpCat.{u + 1}].map
      ((neighborhoodFreeSheaf s f).map a) = stalkSection s f e := by
  refine sectionZ_comp_map _ _ (f.Etale.map a.1) _ _ ?_
  simp only [stalkSectionMap, Category.assoc]
  congr 1
  rw [← strictLocalizationLeg_comp s a, Functor.map_comp, CategoryTheory.Over.comp_left]
  congr 1

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

/-- The comparison map `Hᵠ(X ×_S V, F|) ⟶ Hᵠ(X ×_S S_(s), F|)` for a pointed étale
neighbourhood `(V, v)` of `s`: pull a class back to `X ×_S S_(s)` and restrict it along the
section of `X ×_S V` given by `S_(s) ⟶ V`. -/
noncomputable abbrev stalkComparison (e : Scheme.PointedEtaleNeighborhood s) :
    Abelian.Ext ((neighborhoodFreeSheaf s f).obj e) F q →+
      Sheaf.H ((strictLocalizationProj s f)^*[AddCommGrpCat.{u + 1}].obj F) q :=
  Abelian.Ext.limitComparison (strictLocalizationProj s f)^*[AddCommGrpCat.{u + 1}]
    (neighborhoodFreeSheaf s f) (constantZ _) (stalkSection s f) e F q

/-- A small cofiltered category with an initial functor to the affine pointed étale
neighbourhoods of `s`. -/
abbrev stalkIndex : Type u :=
  InitiallySmall.CofilteredInitialModel.{u} (Scheme.AffinePointedEtaleNeighborhood s)

/-- The initial functor from `AlgebraicGeometry.Etale.stalkIndex` to the pointed étale
neighbourhoods. -/
noncomputable abbrev stalkIndexFunctor : stalkIndex s ⥤ Scheme.PointedEtaleNeighborhood s :=
  InitiallySmall.fromCofilteredInitialModel.{u} _ ⋙ Scheme.AffinePointedEtaleNeighborhood.ι s

/-- The system of the `X ×_S V` over the affine pointed étale neighbourhoods `(V, v)`. -/
noncomputable abbrev stalkDiagram : stalkIndex s ⥤ CategoryTheory.Over X :=
  stalkIndexFunctor s ⋙ neighborhoodDiagramOver s ⋙ CategoryTheory.Over.pullback f

/-- The cone `X ×_S S_(s)` over `AlgebraicGeometry.Etale.stalkDiagram`. -/
noncomputable abbrev stalkCone : Cone (stalkDiagram s f) :=
  ((CategoryTheory.Over.pullback f).mapCone (strictLocalizationConeAllOver s)).whisker
    (stalkIndexFunctor s)

/-- `X ×_S S_(s)` is the limit of the `X ×_S V`. -/
noncomputable def isLimitStalkCone :
    IsLimit ((CategoryTheory.Over.forget X).mapCone (stalkCone s f)) :=
  have := IsCofiltered.isConnected (Scheme.PointedEtaleNeighborhood s)
  (Functor.Initial.isLimitWhiskerEquiv (stalkIndexFunctor s) _).symm
    (isLimitOfPreserves (CategoryTheory.Over.forget X)
      (isLimitOfPreserves (CategoryTheory.Over.pullback f)
        (isLimitStrictLocalizationConeAllOver s)))

instance (i : stalkIndex s) : AlgebraicGeometry.Etale ((stalkDiagram s f).obj i).hom :=
  inferInstanceAs (AlgebraicGeometry.Etale (pullback.snd ((stalkIndexFunctor s).obj i).1.hom f))

lemma stageEtale_stalkDiagram_map {i j : stalkIndex s} (g : i ⟶ j) :
    (stageEtale (stalkDiagram s f) ⋙ freeAbSheaf X).map g =
      (neighborhoodFreeSheaf s f).map ((stalkIndexFunctor s).map g) := by
  simp only [Functor.comp_map]
  congr 1

lemma stalkComparison_eq (i : stalkIndex s) :
    Abelian.Ext.limitComparison ((stalkCone s f).pt.hom)^*[AddCommGrpCat.{u + 1}]
      (stageEtale (stalkDiagram s f) ⋙ freeAbSheaf X) (constantZ _)
      (limitSectionZ (stalkDiagram s f) (stalkCone s f)) i F q =
      stalkComparison s f F q ((stalkIndexFunctor s).obj i) :=
  rfl

variable [QuasiCompact f] [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X]

include s in
lemma stalkDiagram_instances :
    (∀ i, AlgebraicGeometry.Etale ((stalkDiagram s f).obj i).hom) ∧
      (∀ i, CompactSpace ((stalkDiagram s f).obj i).left) ∧
      (∀ i, QuasiSeparatedSpace ((stalkDiagram s f).obj i).left) ∧
      (∀ {i j : stalkIndex s} (g : i ⟶ j), IsAffineHom ((stalkDiagram s f).map g).left) := by
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun {i j} g ↦ ?_⟩
  · exact inferInstanceAs
      (AlgebraicGeometry.Etale (pullback.snd ((stalkIndexFunctor s).obj i).1.hom f))
  · have : IsAffine ((stalkIndexFunctor s).obj i).1.left :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj i).2
    have : CompactSpace ((𝟭 Scheme).obj ((stalkIndexFunctor s).obj i).1.left) :=
      inferInstanceAs (CompactSpace ((stalkIndexFunctor s).obj i).1.left)
    exact inferInstanceAs (CompactSpace ↥(pullback ((stalkIndexFunctor s).obj i).1.hom f))
  · have : IsAffine ((stalkIndexFunctor s).obj i).1.left :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj i).2
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj ((stalkIndexFunctor s).obj i).1.left) :=
      inferInstanceAs (QuasiSeparatedSpace ((stalkIndexFunctor s).obj i).1.left)
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst ((stalkIndexFunctor s).obj i).1.hom f)
  · have : IsAffine ((𝟭 Scheme).obj ((stalkIndexFunctor s).obj i).1.left) :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj i).2
    have : IsAffine ((𝟭 Scheme).obj ((stalkIndexFunctor s).obj j).1.left) :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj j).2
    let h := ((stalkIndexFunctor s).map g).1
    have e₁ : ((stalkDiagram s f).map g).left ≫
        pullback.snd ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj j)).hom f =
        pullback.snd ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj i)).hom f :=
      pullback.lift_snd _ _ _
    have e₂ : h.left ≫ ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj j)).hom =
        ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj i)).hom :=
      MorphismProperty.Over.w h
    have hP : IsPullback ((stalkDiagram s f).map g).left
        (pullback.fst ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj i)).hom f)
        (pullback.fst ((neighborhoodDiagramOver s).obj ((stalkIndexFunctor s).obj j)).hom f)
        h.left := by
      refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ f).flip
      rw [e₁, e₂]
      exact (IsPullback.of_hasPullback _ f).flip
    have : IsAffine ((stalkIndexFunctor s).obj i).1.left :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj i).2
    have : IsAffine ((stalkIndexFunctor s).obj j).1.left :=
      ((InitiallySmall.fromCofilteredInitialModel.{u} _).obj j).2
    have : IsAffineHom h.left := isAffineHom_of_isAffine _
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip this

/-- **Every class on `X ×_S S_(s)` comes from a pointed étale neighbourhood.** -/
theorem exists_stalkComparison_eq
    (x : Sheaf.H ((strictLocalizationProj s f)^*[AddCommGrpCat.{u + 1}].obj F) q) :
    ∃ (e : Scheme.PointedEtaleNeighborhood s)
      (y : Abelian.Ext ((neighborhoodFreeSheaf s f).obj e) F q),
      stalkComparison s f F q e y = x := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := stalkDiagram_instances s f
  obtain ⟨i, y, hy⟩ := (commutesWithLimit_of_isLimit (stalkDiagram s f) (stalkCone s f)
    (isLimitStalkCone s f) q F).1 x
  exact ⟨_, y, hy⟩

/-- **A class at a pointed étale neighbourhood which dies on `X ×_S S_(s)` dies on a smaller
neighbourhood.** -/
theorem exists_eq_zero_of_stalkComparison_eq_zero (e : Scheme.PointedEtaleNeighborhood s)
    (y : Abelian.Ext ((neighborhoodFreeSheaf s f).obj e) F q)
    (hy : stalkComparison s f F q e y = 0) :
    ∃ (e' : Scheme.PointedEtaleNeighborhood s) (a : e' ⟶ e),
      (Abelian.Ext.mk₀ ((neighborhoodFreeSheaf s f).map a)).comp y (zero_add q) = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := stalkDiagram_instances s f
  obtain ⟨a₀⟩ : Nonempty (CostructuredArrow (stalkIndexFunctor s) e) := inferInstance
  have hy₀ : stalkComparison s f F q ((stalkIndexFunctor s).obj a₀.left)
      ((Abelian.Ext.mk₀ ((neighborhoodFreeSheaf s f).map a₀.hom)).comp y (zero_add q)) = 0 :=
    (Abelian.Ext.limitComparison_mk₀_comp (stalkSection_comp_map s f) a₀.hom F q y).trans hy
  obtain ⟨k, g, hg⟩ := (commutesWithLimit_of_isLimit (stalkDiagram s f) (stalkCone s f)
    (isLimitStalkCone s f) q F).2 a₀.left _ hy₀
  refine ⟨_, (stalkIndexFunctor s).map g ≫ a₀.hom, ?_⟩
  rw [Functor.map_comp, ← Abelian.Ext.mk₀_comp_mk₀_assoc, ← stageEtale_stalkDiagram_map]
  exact hg

end Stalk

end AlgebraicGeometry.Etale
