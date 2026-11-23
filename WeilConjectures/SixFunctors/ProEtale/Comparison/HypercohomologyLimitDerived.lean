/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.HypercohomologyLimit
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback
public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestrictionGlobal
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Hypercohomology of pro-étale affines in the derived category

Let `K ∈ D⁺(X_ét, Λ)`, let `U = lim Uᵢ` be a cofiltered limit of affine étale `X`-schemes and let
`L` be a bounded below complex of injective étale sheaves with `Q(L) ≅ K`. We show
`RΓ(U_proét, (ν_X^* K)|_U) ≅ Q(colimᵢ Γ(Uᵢ, L|_{Uᵢ}))` in `D(Λ)`, where the colimit is the
termwise filtered colimit of cochain complexes
(`AlgebraicGeometry.ProEtale.rightDerivedGlobalSectionsIsoSectionsColimit`). Its inverse is the
canonical map: restriction of sections to `U`, followed by `Q(Γ(U, L|_U)) ⟶ RΓ(U_ét, K|_U)` and
the comparison isomorphism `RΓ(U_ét, K|_U) ≅ RΓ(U_proét, (ν_X^* K)|_U)`.

## Main definitions

- `AlgebraicGeometry.Etale.ΓRestrictOver`: for a morphism `f : Y ⟶ Z` of schemes over `S`, the
  restriction of sections `Γ(Z, F|_Z) ⟶ Γ(Y, F|_Y)`, natural in the étale sheaf `F` on `S`.
- `AlgebraicGeometry.Etale.restrictOverSectionsDiagram`: the diagram `i ↦ Γ(Dᵢ, L|_{Dᵢ})` of
  complexes of sections, and `AlgebraicGeometry.Etale.restrictOverSectionsCocone` its cocone of
  restrictions to a cone over `D`.
- `AlgebraicGeometry.ProEtale.sectionsColimitToRightDerivedGlobalSections`: the canonical map
  `Q(colimᵢ Γ(Uᵢ, L|_{Uᵢ})) ⟶ RΓ(U_proét, (ν_X^* K)|_U)`.

## Main results

- `AlgebraicGeometry.Etale.upperStarSectionsUnitQ_comp_globalSectionsRestriction`:
  on a complex `L`, the derived restriction `RΓ(Z, K|_Z) ⟶ RΓ(Y, K|_Y)` is induced by the
  restriction of sections `Γ(Z, L|_Z) ⟶ Γ(Y, L|_Y)`.
- `AlgebraicGeometry.ProEtale.isIso_sectionsColimitToRightDerivedGlobalSections`: the canonical map
  is an isomorphism. In each degree, filtered colimits of modules being exact, this is the
  degreewise statement `AlgebraicGeometry.ProEtale.proEtaleAffineHypercohomologyMap_isColimit`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The components of the inverse of the identity isomorphism `(𝟙 X)_* ≅ 𝟭` of étale
pushforwards are the restriction maps along the identification `V ×_X X ≅ V`. -/
lemma lowerStarId_inv_app_hom_app (X : Scheme.{u}) (G : Sheaf X.smallEtaleTopology A)
    (V : X.Etaleᵒᵖ) :
    ((lowerStarId A X).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ X).hom.app V.unop).op := by
  simp [lowerStarId, GrothendieckTopology.lowerStarId]

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of sections along the identity is the identity, up to `(𝟙 X)^* ≅ 𝟭`. -/
lemma sectionsPullback_id_app_comp (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology A)
    (V : X.Etale) :
    (sectionsPullback A (𝟙 X) (V := V) (W := V) (𝟙 V.left) (by simp)).app F ≫
      ((upperStarId A X).hom.app F).hom.app (op V) = 𝟙 _ := by
  have hu := congr_arg (fun k ↦ k.hom.app (op V)) (upperStarId_hom_app_unit_app A X F)
  have n := ((upperStarId A X).hom.app F).hom.naturality
    (homToPullback (𝟙 X) (𝟙 V.left) (by simp) (V := V) (U := V)).op
  dsimp at hu n
  rw [sectionsPullback_app, assoc]
  erw [n, reassoc_of% hu, lowerStarId_inv_app_hom_app]
  refine (F.obj.map_comp _ _).symm.trans ((congrArg F.obj.map ?_).trans (F.obj.map_id _))
  refine Quiver.Hom.unop_inj ?_
  refine MorphismProperty.Over.Hom.ext ?_
  simp only [MorphismProperty.Over.pullbackId]
  exact homToPullback_left_fst _ _ _

/-- The pullback of global sections along the identity is the identity, up to `(𝟙 X)^* ≅ 𝟭`. -/
@[reassoc]
lemma ΓPullback_id_app (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology A) :
    (ΓPullback A (𝟙 X)).app F ≫
      (Sheaf.Γ X.smallEtaleTopology A).map ((upperStarId A X).hom.app F) = 𝟙 _ := by
  have : IsIso (F.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
    F.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op
  rw [← cancel_mono (F.ΓRes (op (Scheme.Etale.mk (𝟙 X)))), assoc, id_comp]
  erw [Sheaf.ΓRes_naturality]
  have h := ΓPullback_app_comp_ΓRes A (𝟙 X) (V := Scheme.Etale.mk (𝟙 X))
    (W := Scheme.Etale.mk (𝟙 X)) (𝟙 X) (etaleMkId_hom_comp (𝟙 X)) F
  rw [reassoc_of% h]
  erw [sectionsPullback_id_app_comp A X F (Scheme.Etale.mk (𝟙 X))]
  exact comp_id _

/-- For a morphism `f : Y ⟶ Z` of schemes over `S`, the restriction of sections
`Γ(Z, F|_Z) ⟶ Γ(Y, F|_Y)` of an étale sheaf `F` on `S`: the pullback of global sections along
`f` followed by the identification `f^* (F|_Z) ≅ F|_Y`. -/
noncomputable def ΓRestrictOver {S Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z)
    (hf : f ≫ pZ = pY) :
    (pZ)^*[A] ⋙ Sheaf.Γ Z.smallEtaleTopology A ⟶ (pY)^*[A] ⋙ Sheaf.Γ Y.smallEtaleTopology A :=
  Functor.whiskerLeft (pZ)^*[A] (ΓPullback A f) ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (upperStarComp A f pZ pY hf.symm).inv _

lemma ΓRestrictOver_app {S Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z)
    (hf : f ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology A) :
    (ΓRestrictOver A pY pZ f hf).app F = (ΓPullback A f).app ((pZ)^*[A].obj F) ≫
      (Sheaf.Γ Y.smallEtaleTopology A).map ((upperStarComp A f pZ pY hf.symm).inv.app F) := by
  simp [ΓRestrictOver]

/-- The restriction along the identity is the identity. -/
lemma ΓRestrictOver_id {S Z : Scheme.{u}} (pZ : Z ⟶ S) :
    ΓRestrictOver A pZ pZ (𝟙 Z) (id_comp pZ) = 𝟙 _ := by
  ext F
  rw [ΓRestrictOver_app, upperStarComp_id_left]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, NatTrans.id_app]
  erw [comp_id]
  exact ΓPullback_id_app A Z _

/-- The restrictions are compatible with composition. -/
lemma ΓRestrictOver_comp {S W Y Z : Scheme.{u}} (pW : W ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (g : W ⟶ Y) (f : Y ⟶ Z) (hg : g ≫ pY = pW) (hf : f ≫ pZ = pY) :
    ΓRestrictOver A pY pZ f hf ≫ ΓRestrictOver A pW pY g hg =
      ΓRestrictOver A pW pZ (g ≫ f) (by rw [assoc, hf, hg]) := by
  ext F
  simp only [NatTrans.comp_app, ΓRestrictOver_app, assoc]
  have hn := (ΓPullback A g).naturality ((upperStarComp A f pZ pY hf.symm).inv.app F)
  have hc := NatTrans.congr_app (ΓPullback_comp A f g) ((pZ)^*[A].obj F)
  have ha := upperStarComp_hom_app_map_upperStarComp_inv_app A g f pZ (g ≫ f) pY pW rfl
    hf.symm (by rw [assoc, hf, hg]) F
  dsimp at hn hc ha ⊢
  rw [reassoc_of% hn, ← reassoc_of% hc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [reassoc_of% ha, Iso.hom_inv_id_app, comp_id]

/-- The unit `Q(Γ(Z, M)) ⟶ RΓ(Z, Q(M))` of the derived global sections, for a complex `M` of étale
sheaves on `Z`. -/
noncomputable def rightDerivedGlobalSectionsUnitQ {Z : Scheme.{u}}
    (M : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ) :
    DerivedCategory.Q.obj ((Sheaf.Γ Z.smallEtaleTopology A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj M) ⟶
      (rightDerivedGlobalSections A Z).obj (DerivedCategory.Q.obj M) :=
  (Sheaf.Γ Z.smallEtaleTopology A).rightDerivedFunctorUnitQ M

section Complex

variable {S : Scheme.{u}} (I : CochainComplex (Sheaf S.smallEtaleTopology A) ℤ)

lemma mapHomologicalComplex_ΓRestrictOver_app {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) :
    (NatTrans.mapHomologicalComplex (ΓRestrictOver A pY pZ f hf) (ComplexShape.up ℤ)).app I =
      (NatTrans.mapHomologicalComplex (ΓPullback A f) (ComplexShape.up ℤ)).app
          (((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I) ≫
        ((Sheaf.Γ Y.smallEtaleTopology A).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (upperStarComp A f pZ pY hf.symm).inv
            (ComplexShape.up ℤ)).app I) := by
  ext n
  simp [ΓRestrictOver_app]

/-- On a complex `I` of étale sheaves on `S`, the derived restriction
`RΓ(Z, I|_Z) ⟶ RΓ(Y, I|_Y)` along a morphism `f : Y ⟶ Z` over `S` is induced by the restriction
of sections `Γ(Z, I|_Z) ⟶ Γ(Y, I|_Y)`. -/
@[reassoc]
lemma rightDerivedFunctorUnitQ_comp_globalSectionsRestriction {Y Z : Scheme.{u}}
    (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY) :
    rightDerivedGlobalSectionsUnitQ A
        (((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I) ≫
      (rightDerivedGlobalSections A Z).map (((pZ)^*[A]).mapDerivedCategoryFactors.inv.app I) ≫
      globalSectionsRestriction f
        (((pZ)^*[A]).mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
      (rightDerivedGlobalSections A Y).map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp A f pZ pY hf.symm) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar A pZ) (upperStar A f)).symm).inv.app
            (DerivedCategory.Q.obj I)) =
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ΓRestrictOver A pY pZ f hf) (ComplexShape.up ℤ)).app I) ≫
      rightDerivedGlobalSectionsUnitQ A
        (((pY)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I) ≫
      (rightDerivedGlobalSections A Y).map (((pY)^*[A]).mapDerivedCategoryFactors.inv.app I) := by
  unfold rightDerivedGlobalSectionsUnitQ
  rw [← rightDerivedPullback_ΓPullback_app]
  have hnat := (Functor.rightDerivedPullback (f)^*[A] (ΓPullback A f)).naturality
    (((pZ)^*[A]).mapDerivedCategoryFactors.inv.app I)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  erw [reassoc_of% hnat]
  erw [Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app'_assoc]
  rw [mapHomologicalComplex_ΓRestrictOver_app, Functor.map_comp, assoc]
  erw [Functor.rightDerivedFunctorUnitQ_naturality_assoc]
  have key : ((f)^*[A]).mapDerivedCategoryFactors.inv.app
        (((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I) ≫
      ((f)^*[A]).mapDerivedCategory.map (((pZ)^*[A]).mapDerivedCategoryFactors.inv.app I) ≫
      (Functor.mapDerivedCategoryNatIso (upperStarComp A f pZ pY hf.symm) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar A pZ) (upperStar A f)).symm).inv.app
        (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (upperStarComp A f pZ pY hf.symm).inv
          (ComplexShape.up ℤ)).app I) ≫
        ((pY)^*[A]).mapDerivedCategoryFactors.inv.app I := by
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryCompIso_inv_app_Q, Functor.mapDerivedCategoryNatIso_inv_app_Q]
    simp only [assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc,
      Functor.mapHomologicalComplexCompIso_refl_hom_app, DerivedCategory.Q.map_id, id_comp]
  have key' := congrArg (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctor.map key
  simp only [Functor.map_comp] at key'
  exact congrArg (fun t ↦ DerivedCategory.Q.map _ ≫ _ ≫ t) key'

variable {K : DerivedCategory (Sheaf S.smallEtaleTopology A)} {I}

/-- For a complex `I` of étale sheaves on `S` with `e : Q(I) ≅ K` and `pZ : Z ⟶ S`, the canonical
map `Q(Γ(Z, I|_Z)) ⟶ RΓ(Z, K|_Z)`: the unit of the right derived functor of `Γ(Z, -)` at `I|_Z`
followed by `Q(I|_Z) ≅ K|_Z`. It is an isomorphism if `I|_Z` is K-injective. -/
noncomputable def upperStarSectionsUnitQ {Z : Scheme.{u}} (pZ : Z ⟶ S)
    (e : DerivedCategory.Q.obj I ≅ K) :
    DerivedCategory.Q.obj
        (((pZ)^*[A] ⋙ Sheaf.Γ Z.smallEtaleTopology A).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I) ⟶
      (rightDerivedGlobalSections A Z).obj (((pZ)^*[A]).mapDerivedCategory.obj K) :=
  rightDerivedGlobalSectionsUnitQ A
      (((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I) ≫
    (rightDerivedGlobalSections A Z).map
      (((pZ)^*[A]).mapDerivedCategoryFactors.inv.app I ≫
        ((pZ)^*[A]).mapDerivedCategory.map e.hom)

/-- The derived restriction `RΓ(Z, K|_Z) ⟶ RΓ(Y, K|_Y)` along a morphism `f : Y ⟶ Z` over `S`
is induced, through `upperStarSectionsUnitQ`, by the restriction of sections
`Γ(Z, I|_Z) ⟶ Γ(Y, I|_Y)`. -/
@[reassoc]
lemma upperStarSectionsUnitQ_comp_globalSectionsRestriction {Y Z : Scheme.{u}}
    (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
    (e : DerivedCategory.Q.obj I ≅ K) :
    upperStarSectionsUnitQ A pZ e ≫
      globalSectionsRestriction f (((pZ)^*[A]).mapDerivedCategory.obj K) ≫
      (rightDerivedGlobalSections A Y).map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp A f pZ pY hf.symm) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar A pZ) (upperStar A f)).symm).inv.app K) =
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ΓRestrictOver A pY pZ f hf) (ComplexShape.up ℤ)).app I) ≫
      upperStarSectionsUnitQ A pY e := by
  have hn := (Functor.mapDerivedCategoryNatIso (upperStarComp A f pZ pY hf.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar A pZ) (upperStar A f)).symm).inv.naturality e.hom
  have h₁ := globalSectionsRestriction_naturality f (((pZ)^*[A]).mapDerivedCategory.map e.hom)
  have h₂ := rightDerivedFunctorUnitQ_comp_globalSectionsRestriction A I pY pZ f hf
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [upperStarSectionsUnitQ, Functor.map_comp, assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, hn, Functor.map_comp, reassoc_of% h₂]

/-- The degreewise form of
`upperStarSectionsUnitQ_comp_globalSectionsRestriction`. -/
lemma homologyMap_upperStarSectionsUnitQ_comp_hypercohomologyRestrictOver
    {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
    (e : DerivedCategory.Q.obj I ≅ K) (q : ℤ) :
    (DerivedCategory.homologyFunctor A q).map (upperStarSectionsUnitQ A pZ e) ≫
      hypercohomologyRestrictOver A pY pZ f hf K q =
    (DerivedCategory.homologyFunctor A q).map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ΓRestrictOver A pY pZ f hf) (ComplexShape.up ℤ)).app I)) ≫
      (DerivedCategory.homologyFunctor A q).map (upperStarSectionsUnitQ A pY e) := by
  rw [← Functor.map_comp, ← upperStarSectionsUnitQ_comp_globalSectionsRestriction]
  simp only [Functor.map_comp]
  rfl

/-- If `pZ` is étale and `I` is a bounded below complex of injectives, the map
`upperStarSectionsUnitQ` is an isomorphism. -/
lemma isIso_upperStarSectionsUnitQ {Z : Scheme.{u}} (pZ : Z ⟶ S) [Etale pZ]
    [∀ n, Injective (I.X n)] (a : ℤ) [I.IsStrictlyGE a] (e : DerivedCategory.Q.obj I ≅ K) :
    IsIso (upperStarSectionsUnitQ A pZ e) := by
  have (n : ℤ) : Injective ((((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ)).obj I |>.X n) :=
    injective_upperStar_obj_of_etale' A pZ (I.X n)
  have : CochainComplex.IsStrictlyGE
      ((((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact ((pZ)^*[A]).map_isZero (CochainComplex.isZero_of_isStrictlyGE I a i hi)
  have : CochainComplex.IsKInjective
      ((((pZ)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_of_injective _ a
  rw [upperStarSectionsUnitQ, rightDerivedGlobalSectionsUnitQ,
    Functor.rightDerivedFunctorUnitQ_eq]
  exact (((Sheaf.Γ Z.smallEtaleTopology A).rightDerivedFunctorObjQIso _).symm ≪≫
    (rightDerivedGlobalSections A Z).mapIso
      (((pZ)^*[A]).mapDerivedCategoryFactors.symm.app I ≪≫
        ((pZ)^*[A]).mapDerivedCategory.mapIso e)).isIso_hom

end Complex

section Diagram

variable {S : Scheme.{u}} {ι : Type*} [Category* ι] (D : ι ⥤ Over S)
  (I : CochainComplex (Sheaf S.smallEtaleTopology A) ℤ)

lemma ΓRestrictOver_congr {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) {f f' : Y ⟶ Z}
    (h : f = f') (hf : f ≫ pZ = pY) :
    ΓRestrictOver A pY pZ f hf = ΓRestrictOver A pY pZ f' (h ▸ hf) := by
  subst h
  rfl

/-- For a diagram `D` of schemes over `S` and a complex `I` of étale sheaves on `S`, the diagram
of complexes of sections `i ↦ Γ(Dᵢ, I|_{Dᵢ})`, with the restrictions of sections as transition
maps. -/
noncomputable def restrictOverSectionsDiagram : ιᵒᵖ ⥤ CochainComplex A ℤ where
  obj i := (((D.obj i.unop).hom)^*[A] ⋙ Sheaf.Γ (D.obj i.unop).left.smallEtaleTopology A
    ).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj I
  map {i j} g := (NatTrans.mapHomologicalComplex (ΓRestrictOver A (D.obj j.unop).hom
    (D.obj i.unop).hom (D.map g.unop).left (Over.w _)) (ComplexShape.up ℤ)).app I
  map_id i := by
    rw [ΓRestrictOver_congr A _ _ (f' := 𝟙 _) (by simp), ΓRestrictOver_id,
      NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp {i j k} g h := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, ΓRestrictOver_comp]
    exact congrArg (fun φ ↦ (NatTrans.mapHomologicalComplex φ (ComplexShape.up ℤ)).app I)
      (ΓRestrictOver_congr A _ _ (by simp) _)

/-- For a cone `c` over a diagram `D` of schemes over `S`, the restrictions of sections
`Γ(Dᵢ, I|_{Dᵢ}) ⟶ Γ(c, I|_c)` form a cocone. -/
noncomputable def restrictOverSectionsCocone (c : Cone D) :
    Cocone (restrictOverSectionsDiagram A D I) where
  pt := ((c.pt.hom)^*[A] ⋙ Sheaf.Γ c.pt.left.smallEtaleTopology A).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I
  ι :=
    { app i := (NatTrans.mapHomologicalComplex (ΓRestrictOver A c.pt.hom (D.obj i.unop).hom
        (c.π.app i.unop).left (Over.w _)) (ComplexShape.up ℤ)).app I
      naturality {i j} g := by
        dsimp only [restrictOverSectionsDiagram, Functor.const_obj_map]
        refine Eq.trans ?_ (Category.comp_id _).symm
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, ΓRestrictOver_comp]
        exact congrArg (fun φ ↦ (NatTrans.mapHomologicalComplex φ (ComplexShape.up ℤ)).app I)
          (ΓRestrictOver_congr A _ _ (by rw [← Over.comp_left, c.w]) _) }

end Diagram

end Etale

namespace ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  {I : Type u} [SmallCategory I] (D : I ⥤ Over X) (c : Cone D)
  {L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (e : DerivedCategory.Q.obj L ≅ K.obj)

/-- For a cone `c` over a diagram `D` of schemes over `X`, `K ∈ D⁺(X_ét, Λ)` and a complex `L`
with `e : Q(L) ≅ K`, the canonical map `Q(colimᵢ Γ(Dᵢ, L|_{Dᵢ})) ⟶ RΓ(c_proét, (ν_X^* K)|_c)`:
the restrictions of sections `Γ(Dᵢ, L|_{Dᵢ}) ⟶ Γ(c, L|_c)`, followed by the unit
`Q(Γ(c, L|_c)) ⟶ RΓ(c_ét, K|_c)` and the comparison isomorphism
`RΓ(c_ét, K|_c) ≅ RΓ(c_proét, (ν_X^* K)|_c)`. -/
noncomputable def sectionsColimitToRightDerivedGlobalSections :
    DerivedCategory.Q.obj (colimit (Etale.restrictOverSectionsDiagram (ModuleCat.{u + 1} Λ) D L)) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) c.pt.left).obj
        ((ProEtale.upperStar _ c.pt.hom).mapDerivedCategory.obj
          ((comparisonUpperStar _ X).mapDerivedCategory.obj K.obj)) :=
  DerivedCategory.Q.map (colimit.desc _ (Etale.restrictOverSectionsCocone _ D L c)) ≫
    Etale.upperStarSectionsUnitQ _ c.pt.hom e ≫
    (proEtaleAffineRightDerivedGlobalSectionsIso _ c.pt.hom K).hom

/-- In every degree, the canonical map `sectionsColimitToRightDerivedGlobalSections` restricted to
the stage `i` is the canonical map `proEtaleAffineHypercohomologyMap` of the stage. -/
lemma homologyFunctor_map_ι_sectionsColimitToRightDerivedGlobalSections (i : I) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).map (DerivedCategory.Q.map
        (colimit.ι (Etale.restrictOverSectionsDiagram (ModuleCat.{u + 1} Λ) D L) (op i))) ≫
      (DerivedCategory.homologyFunctor _ q).map
        (sectionsColimitToRightDerivedGlobalSections K D c e) =
    (DerivedCategory.homologyFunctor _ q).map
        (Etale.upperStarSectionsUnitQ _ (D.obj i).hom e) ≫
      proEtaleAffineHypercohomologyMap _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)
        K q := by
  rw [← Functor.map_comp, sectionsColimitToRightDerivedGlobalSections,
    ← DerivedCategory.Q.map_comp_assoc, colimit.ι_desc]
  have h := Etale.homologyMap_upperStarSectionsUnitQ_comp_hypercohomologyRestrictOver
    _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) e q
  dsimp only [Etale.restrictOverSectionsCocone]
  rw [Functor.map_comp, Functor.map_comp, ← assoc]
  erw [← h]
  rfl

/-- Filtered colimits of `Λ`-modules indexed by a small cofiltered category are exact. -/
private lemma hasExactColimitsOfShape_moduleCat [IsCofiltered I] :
    HasExactColimitsOfShape Iᵒᵖ (ModuleCat.{u + 1} Λ) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  exact HasExactColimitsOfShape.domain_of_functor Iᵒᵖ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)

/-- **Cohomology of a pro-étale affine, in the derived category.** Let `K ∈ D⁺(X_ét, Λ)` and let
`U = lim Uᵢ` be a cofiltered limit of affine étale `X`-schemes. Let `L` be a bounded below
complex of injective étale sheaves with `e : Q(L) ≅ K`. Then the canonical map
`Q(colimᵢ Γ(Uᵢ, L|_{Uᵢ})) ⟶ RΓ(U_proét, (ν_X^* K)|_U)` is an isomorphism. -/
theorem isIso_sectionsColimitToRightDerivedGlobalSections [IsCofiltered I]
    [∀ i, IsAffine (D.obj i).left] [∀ i, Etale (D.obj i).hom]
    (hc : IsLimit ((Over.forget X).mapCone c)) [∀ n, Injective (L.X n)] (a : ℤ)
    [L.IsStrictlyGE a] :
    IsIso (sectionsColimitToRightDerivedGlobalSections K D c e) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have : HasExactColimitsOfShape Iᵒᵖ (ModuleCat.{u + 1} Λ) := hasExactColimitsOfShape_moduleCat
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  let 𝒞 := Etale.restrictOverSectionsDiagram (ModuleCat.{u + 1} Λ) D L
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q
  let G := DerivedCategory.Q ⋙ H
  have : PreservesColimitsOfShape Iᵒᵖ G :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors _ q).symm
  have hG : IsColimit (G.mapCocone (colimit.cocone 𝒞)) :=
    isColimitOfPreserves G (colimit.isColimit 𝒞)
  have hiso (i : I) : IsIso (H.map (Etale.upperStarSectionsUnitQ _
      (D.obj i).hom e)) := by
    have := Etale.isIso_upperStarSectionsUnitQ _ (D.obj i).hom a e
    infer_instance
  obtain ⟨-, h₂, h₃⟩ := proEtaleAffineHypercohomologyMap_isColimit K D c hc q
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨i⟩, y, rfl⟩ := Concrete.isColimit_exists_rep _ hG z
    have h := ConcreteCategory.congr_hom
      (homologyFunctor_map_ι_sectionsColimitToRightDerivedGlobalSections K D c e i q) y
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    obtain ⟨j, g, hg⟩ := h₃ i _ (h.symm.trans hz)
    have ht := ConcreteCategory.congr_hom
      (Etale.homologyMap_upperStarSectionsUnitQ_comp_hypercohomologyRestrictOver
        _ (D.obj j).hom (D.obj i).hom (D.map g).left (Over.w _) e q) y
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hg] at ht
    have hy : G.map (𝒞.map g.op) y = 0 :=
      ((ConcreteCategory.isIso_iff_bijective _).1 (hiso j)).1 (ht.symm.trans (map_zero _).symm)
    change G.map (colimit.ι 𝒞 (op i)) y = 0
    rw [← colimit.w 𝒞 g.op, Functor.map_comp, ConcreteCategory.comp_apply, hy, map_zero]
  · intro x
    obtain ⟨i, y, rfl⟩ := h₂ x
    refine ⟨G.map (colimit.ι 𝒞 (op i)) (inv (H.map (Etale.upperStarSectionsUnitQ _
      (D.obj i).hom e)) y), ?_⟩
    have h := ConcreteCategory.congr_hom
      (homologyFunctor_map_ι_sectionsColimitToRightDerivedGlobalSections K D c e i q)
      (inv (H.map (Etale.upperStarSectionsUnitQ _ (D.obj i).hom e)) y)
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, IsIso.inv_hom_id_apply] at h
    exact h

/-- **Cohomology of a pro-étale affine, in the derived category** (the isomorphism). Let
`K ∈ D⁺(X_ét, Λ)` and let `U = lim Uᵢ` be a cofiltered limit of affine étale `X`-schemes. For a
bounded below complex `L` of injective étale sheaves with `e : Q(L) ≅ K`,
`RΓ(U_proét, (ν_X^* K)|_U) ≅ Q(colimᵢ Γ(Uᵢ, L|_{Uᵢ}))`, where the colimit is the termwise
filtered colimit of cochain complexes. Its inverse is the canonical map
`sectionsColimitToRightDerivedGlobalSections`. -/
noncomputable def rightDerivedGlobalSectionsIsoSectionsColimit [IsCofiltered I]
    [∀ i, IsAffine (D.obj i).left] [∀ i, Etale (D.obj i).hom]
    (hc : IsLimit ((Over.forget X).mapCone c)) [∀ n, Injective (L.X n)] (a : ℤ)
    [L.IsStrictlyGE a] :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) c.pt.left).obj
        ((ProEtale.upperStar _ c.pt.hom).mapDerivedCategory.obj
          ((comparisonUpperStar _ X).mapDerivedCategory.obj K.obj)) ≅
      DerivedCategory.Q.obj
        (colimit (Etale.restrictOverSectionsDiagram (ModuleCat.{u + 1} Λ) D L)) :=
  have := isIso_sectionsColimitToRightDerivedGlobalSections K D c e hc a
  (asIso (sectionsColimitToRightDerivedGlobalSections K D c e)).symm

@[simp]
lemma rightDerivedGlobalSectionsIsoSectionsColimit_inv [IsCofiltered I]
    [∀ i, IsAffine (D.obj i).left] [∀ i, Etale (D.obj i).hom]
    (hc : IsLimit ((Over.forget X).mapCone c)) [∀ n, Injective (L.X n)] (a : ℤ)
    [L.IsStrictlyGE a] :
    (rightDerivedGlobalSectionsIsoSectionsColimit K D c e hc a).inv =
      sectionsColimitToRightDerivedGlobalSections K D c e :=
  rfl

end ProEtale

end AlgebraicGeometry
