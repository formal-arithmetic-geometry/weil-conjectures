/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# The long exact sequence of cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`. For an injective étale sheaf `I`
on `X` the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism, so for a complex `I` of injective
sheaves

`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`

is a short exact sequence of complexes. Its triangle identifies, for every complex `K` (represented
by its functorial K-injective resolution, which has injective components), with a distinguished
triangle

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`

whose first two maps are induced by the inclusion of sections with support and by the
restriction, and whose connecting morphism is natural in `K`. Taking cohomology gives the long
exact sequence

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ ⋯`.

Here `RΓ(U, -)` is the right derived functor of the sections over the étale `X`-scheme `U`.

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`
- `AlgebraicGeometry.Etale.sectionsWithSupportδ`: the connecting morphism, a natural
  transformation `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]`
- `AlgebraicGeometry.Etale.distTriang_rightDerivedSectionsWithSupport`
- `AlgebraicGeometry.Etale.exact_derivedSupportCohomology`,
  `AlgebraicGeometry.Etale.homologyMap_sectionsWithSupportδ_naturality`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

/-- On a K-injective complex `I`, the natural transformation `RF ⟶ RG` induced by `τ : F ⟶ G` is
`τ` applied termwise, through the identifications `RF(I) ≅ F(I)` and `RG(I) ≅ G(I)`. -/
lemma rightDerivedFunctorNatTrans_app_Q_obj {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (I : CochainComplex C ℤ) [I.IsKInjective] :
    (rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj I) ≫
        (G.rightDerivedFunctorObjQIso I).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ _).app I) := by
  have h₁ := (rightDerivedFunctorNatTrans τ).naturality
    ((DerivedCategory.quotientCompQhIso C).inv.app I)
  have h₂ : F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (rightDerivedFunctorNatTrans τ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex τ _).app I)) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) :=
    rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
      F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh) ((HomotopyCategory.quotient _ _).obj I)
  have h₃ := (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((NatTrans.mapHomologicalComplex τ _).app I)
  dsimp at h₁ h₃
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← reassoc_of% h₁]
  simp only [assoc]
  congr 1
  rw [← cancel_epi (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)),
    IsIso.hom_inv_id_assoc, reassoc_of% h₂, IsIso.hom_inv_id_assoc]
  exact h₃


/-- The identification `R(F)(Q I) ≅ Q (F I)` on K-injective complexes is natural in morphisms of
K-injective complexes. -/
@[reassoc]
lemma rightDerivedFunctorObjQIso_hom_naturality (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (φ : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map φ) ≫ (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex _).map φ) := by
  have h₁ := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map φ)
  have h₂ := (DerivedCategory.quotientCompQhIso C).inv.naturality φ
  have h₃ := (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((F.mapHomologicalComplex _).map φ)
  dsimp at h₁ h₂ h₃
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  have key : F.rightDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map φ)) ≫
        CategoryTheory.inv (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)) =
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((F.mapHomologicalComplex _).map φ)) := by
    rw [IsIso.comp_inv_eq, assoc, h₁, IsIso.inv_hom_id_assoc]
  rw [← F.rightDerivedFunctor.map_comp_assoc, h₂, F.rightDerivedFunctor.map_comp_assoc,
    reassoc_of% key, assoc, assoc]
  erw [h₃]

end CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Every morphism `Q(I) ⟶ Q(J)` in the derived category to the image of a K-injective complex
`J` is induced by a morphism of complexes. -/
lemma Q_map_surjective_of_isKInjective {I J : CochainComplex C ℤ} [J.IsKInjective]
    (g : Q.obj I ⟶ Q.obj J) : ∃ φ : I ⟶ J, Q.map φ = g := by
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).2
      ((quotientCompQhIso C).hom.app I ≫ g ≫ (quotientCompQhIso C).inv.app J)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
  refine ⟨φ, ?_⟩
  have h := (quotientCompQhIso C).hom.naturality φ
  dsimp at h hψ
  rw [hψ, assoc, assoc, Iso.inv_hom_id_app, comp_id] at h
  exact ((cancel_epi _).1 h).symm

end DerivedCategory


namespace CategoryTheory

/-- The sections of sheaves over an object of the site form an additive functor. -/
instance Sheaf.additive_sheafSections_obj {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] [Preadditive A] (U : Cᵒᵖ) : ((sheafSections J A).obj U).Additive where
  map_add := rfl

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
lemma isIso_of_isIso_left {V W : X.Etale} (f : V ⟶ W) (hf : IsIso f.left) : IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `U ×_X U ⟶ U` at `U` of the adjunction between composition with and base change
along the open immersion `j` is an isomorphism, `j` being a monomorphism. -/
instance isIso_mapPullbackAdj_counit_app_mk :
    IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app
      (Scheme.Etale.mk j)) :=
  isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
instance isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map
      ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j))) := by
  refine isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map
    ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
instance isIso_lowerStar_obj_map_isTerminalMkId_from (G : Sheaf U.smallEtaleTopology A) :
    IsIso (((j)_*[A].obj G).obj.map ((Scheme.Etale.isTerminalMkId X).from
      (Scheme.Etale.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
instance isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf X.smallEtaleTopology A) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction A j).unit.app M).hom.app
      (op (Scheme.Etale.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app (Scheme.Etale.mk j)).op ≫ 𝟙 _))

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
lemma ΓRes_eq (M : Sheaf X.smallEtaleTopology A) :
    M.ΓRes (op (Scheme.Etale.mk j)) =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)).op :=
  (M.ΓRes_map _).symm

instance (M : Sheaf X.smallEtaleTopology A) : IsIso (M.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op

/-- If the unit `M ⟶ j_* j^* M` of the restriction along the open immersion `j` is a split
epimorphism, the restriction `Γ(X, M) ⟶ M(U)` of global sections is a split epimorphism. In the
square

```
M(X) ───────────▶ M(U)
 │ η_X               │ η_U ≅
 ▼                   ▼
(j_* j^* M)(X) ──≅──▶ (j_* j^* M)(U)
```

the bottom map and `η_U` are isomorphisms and `η_X` is split by the section of the unit. -/
lemma isSplitEpi_ΓRes_of_isSplitEpi_unit (M : Sheaf X.smallEtaleTopology A)
    [IsSplitEpi ((openImmersionRestrictionLowerStarAdjunction A j).unit.app M)] :
    IsSplitEpi (M.ΓRes (op (Scheme.Etale.mk j))) := by
  set η := (openImmersionRestrictionLowerStarAdjunction A j).unit.app M
  set t := (Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)
  set σ := section_ η
  have hσ : σ.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ η.hom.app (op (Scheme.Etale.mk (𝟙 X))) =
      𝟙 _ := by
    have h := (sheafToPresheaf _ A).congr_map (IsSplitEpi.id η)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact congr_app h _
  have hsq : M.obj.map t.op ≫ η.hom.app (op (Scheme.Etale.mk j)) =
      η.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        ((j)_*[A].obj (openImmersionRestriction A j |>.obj M)).obj.map t.op :=
    η.hom.naturality t.op
  have : IsSplitEpi (M.obj.map t.op) :=
    ⟨⟨η.hom.app (op (Scheme.Etale.mk j)) ≫
        inv (((j)_*[A].obj (openImmersionRestriction A j |>.obj M)).obj.map t.op) ≫
          σ.hom.app (op (Scheme.Etale.mk (𝟙 X))), by
      rw [← cancel_mono (η.hom.app (op (Scheme.Etale.mk j))), assoc, assoc, hsq]
      simp only [assoc]
      rw [reassoc_of% hσ, IsIso.inv_hom_id, comp_id, id_comp]⟩⟩
  rw [ΓRes_eq]
  infer_instance

end Restriction

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
/-- For an injective étale sheaf `I` on `X` and a closed immersion `i : Z ⟶ X` with open
complement `U`, the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism: the restriction
`I ⟶ j_* j^* I` to the open part is a split epimorphism
(`AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`). -/
theorem isSplitEpi_ΓRes_openComplement_of_injective (I : Sheaf X.smallEtaleTopology A)
    [Injective I] : IsSplitEpi (I.ΓRes (op (Scheme.Etale.mk i.openComplement.ι))) := by
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A i.openComplement.ι i
    i.range_eq_compl_range_openComplement_ι I
  have : IsSplitEpi ((openImmersionRestrictionLowerStarAdjunction A i.openComplement.ι).unit.app
      I) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A _)
      (openImmersionRestrictionLowerStarAdjunction A i.openComplement.ι)]
    infer_instance
  exact isSplitEpi_ΓRes_of_isSplitEpi_unit A _ I


/-- The sequence `Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I)` of complexes of a complex `I` of étale sheaves:
the inclusion of the sections with support in `Z`, and the restriction to the open complement
`U` of `Z`. -/
@[simps]
noncomputable def sectionsWithSupportShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (Sheaf.ΓSupportι X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    ((NatTrans.mapHomologicalComplex (Sheaf.natTransΓRes X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    (by ext n; simp)

include hJX hJZ in
/-- For a complex `I` of injective sheaves, `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is a short
exact sequence of complexes: degreewise, `Γ_Z` is the kernel of the restriction, which is a
split epimorphism (`AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`). -/
theorem shortExact_sectionsWithSupportShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    (sectionsWithSupportShortComplex A i I).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have := isSplitEpi_ΓRes_openComplement_of_injective A i (I.X n)
  have hκ := KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι)))) ((evaluation _ A).obj (I.X n))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hκ) ?_ ?_
  · change Mono ((Sheaf.ΓSupportι X.smallEtaleTopology A _).app (I.X n))
    infer_instance
  · change Epi ((I.X n).ΓRes _)
    infer_instance

/-- A morphism `φ : I ⟶ J` of complexes of injective sheaves induces a morphism of the short
exact sequences `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` and `0 ⟶ Γ_Z(X, J) ⟶ Γ(X, J) ⟶ Γ(U, J) ⟶ 0`
of `AlgebraicGeometry.Etale.sectionsWithSupportShortComplex`. -/
@[simps]
noncomputable def sectionsWithSupportShortComplexMap
    {I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ} (φ : I ⟶ J) :
    sectionsWithSupportShortComplex A i I ⟶ sectionsWithSupportShortComplex A i J where
  τ₁ := ((Sheaf.ΓSupport X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι))).mapHomologicalComplex _).map φ
  τ₂ := ((Sheaf.Γ X.smallEtaleTopology A).mapHomologicalComplex _).map φ
  τ₃ := (((sheafSections X.smallEtaleTopology A).obj
    (op (Scheme.Etale.mk i.openComplement.ι))).mapHomologicalComplex _).map φ
  comm₁₂ := (NatTrans.mapHomologicalComplex _ _).naturality φ
  comm₂₃ := (NatTrans.mapHomologicalComplex _ _).naturality φ

include hJX hJZ in
/-- The connecting morphism `RΓ(U, I) ⟶ RΓ_Z(X, I)[1]` of a K-injective complex `I` of injective
sheaves: the connecting morphism of the triangle of the short exact sequence
`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`
(`AlgebraicGeometry.Etale.shortExact_sectionsWithSupportShortComplex`), through the
identifications `RF(I) ≅ F(I)` of the derived functors on K-injective complexes. -/
noncomputable def sectionsWithSupportδQObj
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)]
    [I.IsKInjective] :
    ((sheafSections X.smallEtaleTopology A).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I) ⟶
      ((Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I))⟦(1 : ℤ)⟧ :=
  (((sheafSections X.smallEtaleTopology A).obj
      (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctorObjQIso I).hom ≫
    DerivedCategory.triangleOfSESδ (shortExact_sectionsWithSupportShortComplex A i I) ≫
      ((Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctorObjQIso I).inv⟦(1 : ℤ)⟧'

include hJX hJZ in
/-- The connecting morphism `AlgebraicGeometry.Etale.sectionsWithSupportδQObj` is natural in
morphisms of K-injective complexes of injective sheaves. -/
@[reassoc]
lemma sectionsWithSupportδQObj_naturality
    {I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ} [∀ n, Injective (I.X n)]
    [I.IsKInjective] [∀ n, Injective (J.X n)] [J.IsKInjective] (φ : I ⟶ J) :
    ((sheafSections X.smallEtaleTopology A).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map
          (DerivedCategory.Q.map φ) ≫ sectionsWithSupportδQObj A i J =
      sectionsWithSupportδQObj A i I ≫ ((Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map
          (DerivedCategory.Q.map φ))⟦(1 : ℤ)⟧' := by
  set Uo := op (Scheme.Etale.mk i.openComplement.ι)
  have h₁ := Functor.rightDerivedFunctorObjQIso_hom_naturality
    (Sheaf.ΓSupport X.smallEtaleTopology A Uo) φ
  have h₃ := Functor.rightDerivedFunctorObjQIso_hom_naturality
    ((sheafSections X.smallEtaleTopology A).obj Uo) φ
  have hδ := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_sectionsWithSupportShortComplex A i I)
    (shortExact_sectionsWithSupportShortComplex A i J) (sectionsWithSupportShortComplexMap A i φ)
  have h₁' : ((Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctorObjQIso I).inv ≫
      (Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctor.map
        (DerivedCategory.Q.map φ) =
      DerivedCategory.Q.map (((Sheaf.ΓSupport X.smallEtaleTopology A Uo).mapHomologicalComplex
        _).map φ) ≫ ((Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctorObjQIso J).inv
      := by
    rw [Iso.inv_comp_eq, ← reassoc_of% h₁, Iso.hom_inv_id, comp_id]
  simp only [sectionsWithSupportδQObj, assoc]
  rw [reassoc_of% h₃]
  congr 1
  rw [← Functor.map_comp, h₁', Functor.map_comp]
  erw [← reassoc_of% hδ]
  rfl

/-- The K-injective complex of injective sheaves representing an object `K` of the derived
category: the functorial K-injective resolution
(`CochainComplex.kInjectiveResolutionFunctor`) of a complex representing `K`. -/
noncomputable abbrev sectionsWithSupportResolution
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    CochainComplex (Sheaf X.smallEtaleTopology A) ℤ :=
  (CochainComplex.kInjectiveResolutionFunctor.{u + 1} _).obj (DerivedCategory.Q.objPreimage K)

/-- The isomorphism `Q(I) ≅ K` for the resolution `I` of
`AlgebraicGeometry.Etale.sectionsWithSupportResolution`. -/
noncomputable def sectionsWithSupportResolutionIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.Q.obj (sectionsWithSupportResolution A K) ≅ K :=
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} _).app
      (DerivedCategory.Q.objPreimage K)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ _).2
  (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{u + 1} _).app
    (DerivedCategory.Q.objPreimage K)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

include hJX hJZ in
/-- The connecting morphism `δ : RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` of the triangle of cohomology with
support in `Z`, as a natural transformation: on a K-injective complex of injective sheaves it is
`AlgebraicGeometry.Etale.sectionsWithSupportδQObj`, the connecting morphism of the short exact
sequence `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`, and in general it is transported along the
functorial K-injective resolution. -/
noncomputable def sectionsWithSupportδ :
    ((sheafSections X.smallEtaleTopology A).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor ⟶
      (Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor ⋙
          shiftFunctor _ (1 : ℤ) where
  app K := ((sheafSections X.smallEtaleTopology A).obj
      (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map
        (sectionsWithSupportResolutionIso A K).inv ≫
    sectionsWithSupportδQObj A i (sectionsWithSupportResolution A K) ≫
      ((Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map
          (sectionsWithSupportResolutionIso A K).hom)⟦(1 : ℤ)⟧'
  naturality K L f := by
    set Uo := op (Scheme.Etale.mk i.openComplement.ι)
    set F₁ := (Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctor
    set F₃ := ((sheafSections X.smallEtaleTopology A).obj Uo).rightDerivedFunctor
    set eK := sectionsWithSupportResolutionIso A K
    set eL := sectionsWithSupportResolutionIso A L
    obtain ⟨φ, hφ⟩ := DerivedCategory.Q_map_surjective_of_isKInjective
      (eK.hom ≫ f ≫ eL.inv)
    have h₁ : f ≫ eL.inv = eK.inv ≫ DerivedCategory.Q.map φ := by
      rw [hφ, Iso.inv_hom_id_assoc]
    have h₂ : DerivedCategory.Q.map φ ≫ eL.hom = eK.hom ≫ f := by
      rw [hφ, assoc, assoc, Iso.inv_hom_id, comp_id]
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [← F₃.map_comp_assoc, h₁, F₃.map_comp_assoc, sectionsWithSupportδQObj_naturality_assoc,
      ← Functor.map_comp, ← Functor.map_comp, h₂, Functor.map_comp, Functor.map_comp, assoc, assoc]

include hJX hJZ in
/-- On a K-injective complex `I` of injective sheaves, the connecting morphism
`AlgebraicGeometry.Etale.sectionsWithSupportδ` is the connecting morphism
`AlgebraicGeometry.Etale.sectionsWithSupportδQObj` of the short exact sequence
`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`. -/
lemma sectionsWithSupportδ_app_Q_obj
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)]
    [I.IsKInjective] :
    (sectionsWithSupportδ A i).app (DerivedCategory.Q.obj I) = sectionsWithSupportδQObj A i I := by
  set Uo := op (Scheme.Etale.mk i.openComplement.ι)
  set e := sectionsWithSupportResolutionIso A (DerivedCategory.Q.obj I)
  obtain ⟨φ, hφ⟩ := DerivedCategory.Q_map_surjective_of_isKInjective e.inv
  have h := sectionsWithSupportδQObj_naturality A i φ
  simp only [sectionsWithSupportδ]
  rw [← hφ, reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp, hφ, e.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, comp_id]

include hJX hJZ in
/-- For a K-injective complex `I` of injective sheaves, the derived functors of the sections
with support, of the global sections and of the sections over `U` fit in the distinguished
triangle `RΓ_Z(X, I) ⟶ RΓ(X, I) ⟶ RΓ(U, I) ⟶ RΓ_Z(X, I)[1]` whose first two maps are induced by
the inclusion and the restriction and whose third map is
`AlgebraicGeometry.Etale.sectionsWithSupportδQObj`: it is isomorphic to the triangle of the
short exact sequence `AlgebraicGeometry.Etale.shortExact_sectionsWithSupportShortComplex`. -/
theorem distTriang_rightDerivedSectionsWithSupport_Q_obj
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)]
    [I.IsKInjective] :
    Triangle.mk ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology
        A (op (Scheme.Etale.mk i.openComplement.ι)))).app (DerivedCategory.Q.obj I))
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app (DerivedCategory.Q.obj I))
      (sectionsWithSupportδQObj A i I) ∈ distTriang _ := by
  have hS := shortExact_sectionsWithSupportShortComplex A i I
  let e₁ := (Sheaf.ΓSupport X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctorObjQIso I
  let e₂ := (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorObjQIso I
  let e₃ := ((sheafSections X.smallEtaleTopology A).obj
    (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctorObjQIso I
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · simp only [Triangle.mk_mor₃, sectionsWithSupportδQObj, e₁, e₃, assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id]
    rfl

include hJX hJZ in
/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`, and `K` a complex of étale
sheaves on `X` (for instance a sheaf placed in degree `0`). The maps
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K)` induced by the inclusion of the sections with support in `Z`
and by the restriction to `U`, together with the connecting morphism
`δ : RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` (`AlgebraicGeometry.Etale.sectionsWithSupportδ`, natural in `K`),
form a distinguished triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`.

Represent `K` by a K-injective complex `I` of injective sheaves. For an injective sheaf the
restriction `Γ(X, I) ⟶ I(U)` is surjective, so `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is a short
exact sequence of complexes, and its triangle is the one of the statement. The long exact
cohomology sequence is `AlgebraicGeometry.Etale.exact_derivedSupportCohomology`. -/
theorem distTriang_rightDerivedSectionsWithSupport
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Triangle.mk ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology
        A (op (Scheme.Etale.mk i.openComplement.ι)))).app K)
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app K)
      ((sectionsWithSupportδ A i).app K) ∈ distTriang _ := by
  set Uo := op (Scheme.Etale.mk i.openComplement.ι)
  set I := sectionsWithSupportResolution A K
  set eK := sectionsWithSupportResolutionIso A K
  have hδ := distTriang_rightDerivedSectionsWithSupport_Q_obj A i I
  let F₁ := (Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctor
  let F₃ := ((sheafSections X.smallEtaleTopology A).obj Uo).rightDerivedFunctor
  refine isomorphic_distinguished _ hδ _
    (Triangle.isoMk _ _ (F₁.mapIso eK.symm)
      ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.mapIso eK.symm)
      (F₃.mapIso eK.symm) ?_ ?_ ?_)
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality eK.inv).symm
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality eK.inv).symm
  · simp only [Triangle.mk_mor₃, Iso.symm_hom, Functor.mapIso_hom]
    exact ((sectionsWithSupportδ A i).naturality eK.inv).symm.trans
      (by rw [sectionsWithSupportδ_app_Q_obj])

include hJX hJZ in
/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**The long exact sequence.** For a complex `K` of étale sheaves on `X` (e.g. a sheaf in degree
`0`) and a closed immersion `i : Z ⟶ X` with open complement `U`,

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ H^{q+1}(X, K) ⟶ ⋯`

is exact. Here `H^q_Z(X, K) = H^q(RΓ_Z(X, K))`
(`AlgebraicGeometry.Etale.derivedSupportCohomology`), the first two maps are induced by the
inclusion of sections with support and the restriction, and the connecting maps
`H^q(U, K) ⟶ H^{q+1}_Z(X, K)` are those of the triangle
`AlgebraicGeometry.Etale.distTriang_rightDerivedSectionsWithSupport`, induced by the connecting
morphism `AlgebraicGeometry.Etale.sectionsWithSupportδ`. All maps are natural in `K`: the first
two are induced by natural transformations, and the connecting maps by the natural
transformation `sectionsWithSupportδ`
(`AlgebraicGeometry.Etale.homologyMap_sectionsWithSupportδ_naturality`). -/
theorem exact_derivedSupportCohomology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (q₀ q₁ : ℤ) (h : q₀ + 1 = q₁) :
    (ShortComplex.mk ((DerivedCategory.homologyFunctor A q₀).map
        ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology A
          (op (Scheme.Etale.mk i.openComplement.ι)))).app K))
      ((DerivedCategory.homologyFunctor A q₀).map
        ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
          (op (Scheme.Etale.mk i.openComplement.ι)))).app K))
      (by rw [← Functor.map_comp]
          erw [comp_distTriang_mor_zero₁₂ _ (distTriang_rightDerivedSectionsWithSupport A i K)]
          exact Functor.map_zero _ _ _)).Exact ∧
    (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.comp_δ _
      (distTriang_rightDerivedSectionsWithSupport A i K) q₀ q₁ h)).Exact ∧
    (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.δ_comp _
      (distTriang_rightDerivedSectionsWithSupport A i K) q₀ q₁ h)).Exact :=
  ⟨DerivedCategory.HomologySequence.exact₂ _ (distTriang_rightDerivedSectionsWithSupport A i K) q₀,
    DerivedCategory.HomologySequence.exact₃ _ (distTriang_rightDerivedSectionsWithSupport A i K)
      q₀ q₁ h,
    DerivedCategory.HomologySequence.exact₁ _ (distTriang_rightDerivedSectionsWithSupport A i K)
      q₀ q₁ h⟩

include hJX hJZ in
/-- The connecting maps `H^q(U, K) ⟶ H^{q+1}_Z(X, K)` of the long exact sequence of cohomology
with support (`AlgebraicGeometry.Etale.exact_derivedSupportCohomology`) are natural in `K`. -/
lemma homologyMap_sectionsWithSupportδ_naturality
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ L) (q₀ q₁ : ℤ)
    (h : 1 + q₀ = q₁) :
    (DerivedCategory.homologyFunctor A q₀).map (((sheafSections X.smallEtaleTopology A).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map f) ≫
      (DerivedCategory.homologyFunctor A 0).shiftMap ((sectionsWithSupportδ A i).app L) q₀ q₁ h =
    (DerivedCategory.homologyFunctor A 0).shiftMap ((sectionsWithSupportδ A i).app K) q₀ q₁ h ≫
      (DerivedCategory.homologyFunctor A q₁).map ((Sheaf.ΓSupport X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map f) := by
  have := (sectionsWithSupportδ A i).naturality f
  dsimp only [Functor.comp_map] at this
  have h₁ := (DerivedCategory.homologyFunctor A 0).shiftMap_comp' (((sheafSections
    X.smallEtaleTopology A).obj (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map
      f) ((sectionsWithSupportδ A i).app L) q₀ q₁ h
  have h₂ := (DerivedCategory.homologyFunctor A 0).shiftMap_comp ((sectionsWithSupportδ A i).app K)
    ((Sheaf.ΓSupport X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor.map f) q₀ q₁ h
  rw [this] at h₁
  exact h₁.symm.trans h₂

end Concrete

end Etale

end AlgebraicGeometry
