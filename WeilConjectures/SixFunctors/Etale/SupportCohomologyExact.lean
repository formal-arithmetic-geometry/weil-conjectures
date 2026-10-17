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
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# The long exact sequence of cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`. For an injective étale sheaf `I`
on `X` the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism, so for a complex `I` of injective
sheaves

`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`

is a short exact sequence of complexes. Its triangle identifies, for a bounded below complex `K`,
with a distinguished triangle

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`

whose first two maps are induced by the inclusion of sections with support and by the
restriction, and taking cohomology gives the long exact sequence

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ ⋯`.

Here `RΓ(U, -)` is the right derived functor of the sections over the étale `X`-scheme `U`.

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`
- `AlgebraicGeometry.Etale.exists_distTriang_rightDerivedSectionsWithSupport`
- `AlgebraicGeometry.Etale.exact_derivedSupportCohomology`
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

end CategoryTheory.Functor

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

variable [HasSmallSiteSheafify A]

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

include hJX hJZ in
/-- For a K-injective complex `I` of injective sheaves, the derived functors of the sections
with support, of the global sections and of the sections over `U` fit in a distinguished
triangle `RΓ_Z(X, I) ⟶ RΓ(X, I) ⟶ RΓ(U, I) ⟶ RΓ_Z(X, I)[1]`, whose first two maps are induced by
the inclusion and the restriction: it is isomorphic to the triangle of the short exact sequence
`AlgebraicGeometry.Etale.shortExact_sectionsWithSupportShortComplex`. -/
theorem exists_distTriang_rightDerivedSectionsWithSupport_Q_obj
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)]
    [I.IsKInjective] :
    ∃ δ, Triangle.mk ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology
        A (op (Scheme.Etale.mk i.openComplement.ι)))).app (DerivedCategory.Q.obj I))
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app (DerivedCategory.Q.obj I)) δ ∈
          distTriang _ := by
  set Uo := op (Scheme.Etale.mk i.openComplement.ι)
  have hS := shortExact_sectionsWithSupportShortComplex A i I
  let e₁ := (Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctorObjQIso I
  let e₂ := (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorObjQIso I
  let e₃ := ((sheafSections X.smallEtaleTopology A).obj Uo).rightDerivedFunctorObjQIso I
  refine ⟨e₃.hom ≫ (DerivedCategory.triangleOfSES hS).mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · simp only [Triangle.mk_mor₃, Triangle.mk_obj₁, Iso.symm_hom, Functor.mapIso_hom]
    simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      comp_id]

include hJX hJZ in
/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`, and `K` a bounded below complex
of étale sheaves on `X` (for instance a sheaf placed in degree `0`). The maps
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K)` induced by the inclusion of the sections with support in `Z`
and by the restriction to `U` extend to a distinguished triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`.

Represent `K` by a bounded below complex `I` of injective sheaves. For an injective sheaf the
restriction `Γ(X, I) ⟶ I(U)` is surjective, so `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is a short
exact sequence of complexes, and its triangle is the one of the statement. The long exact
cohomology sequence is `AlgebraicGeometry.Etale.exact_derivedSupportCohomology`. -/
theorem exists_distTriang_rightDerivedSectionsWithSupport
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) [K.IsGE n] :
    ∃ δ, Triangle.mk ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology
        A (op (Scheme.Etale.mk i.openComplement.ι)))).app K)
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app K) δ ∈ distTriang _ := by
  set Uo := op (Scheme.Etale.mk i.openComplement.ι)
  obtain ⟨L, _, ⟨eL⟩⟩ := K.exists_iso_Q_obj_of_isGE n
  obtain ⟨R, -, hR⟩ := CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE L n
  have : IsIso (DerivedCategory.Q.map R.ι) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eK : DerivedCategory.Q.obj R.I ≅ K := (asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ eL.symm
  obtain ⟨δ, hδ⟩ := exists_distTriang_rightDerivedSectionsWithSupport_Q_obj A i R.I
  let F₁ := (Sheaf.ΓSupport X.smallEtaleTopology A Uo).rightDerivedFunctor
  let F₃ := ((sheafSections X.smallEtaleTopology A).obj Uo).rightDerivedFunctor
  refine ⟨F₃.map eK.inv ≫ δ ≫ (F₁.map eK.hom)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hδ _
    (Triangle.isoMk _ _ (F₁.mapIso eK.symm)
      ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.mapIso eK.symm)
      (F₃.mapIso eK.symm) ?_ ?_ ?_)⟩
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality eK.inv).symm
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality eK.inv).symm
  · simp only [Triangle.mk_mor₃, Triangle.mk_obj₁, Iso.symm_hom, Functor.mapIso_hom]
    simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      comp_id, F₁]

include hJX hJZ in
/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**The long exact sequence.** For a bounded below complex `K` of étale sheaves on `X` (e.g. a
sheaf in degree `0`) and a closed immersion `i : Z ⟶ X` with open complement `U`, there are
connecting maps `δ : H^q(U, K) ⟶ H^{q+1}_Z(X, K)` such that

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ H^{q+1}(X, K) ⟶ ⋯`

is exact. Here `H^q_Z(X, K) = H^q(RΓ_Z(X, K))`
(`AlgebraicGeometry.Etale.derivedSupportCohomology`), and the first two maps are induced by the
inclusion of sections with support and the restriction; all maps are natural in `K`, the first
two by construction. The sequence is the homology sequence of the triangle
`AlgebraicGeometry.Etale.exists_distTriang_rightDerivedSectionsWithSupport`. -/
theorem exact_derivedSupportCohomology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) [K.IsGE n] :
    ∃ δ, ∃ hT : Triangle.mk ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι
        X.smallEtaleTopology A (op (Scheme.Etale.mk i.openComplement.ι)))).app K)
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app K) δ ∈ distTriang _,
      ∀ (q₀ q₁ : ℤ) (h : q₀ + 1 = q₁),
        (ShortComplex.mk ((DerivedCategory.homologyFunctor A q₀).map
            ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology A
              (op (Scheme.Etale.mk i.openComplement.ι)))).app K))
          ((DerivedCategory.homologyFunctor A q₀).map
            ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
              (op (Scheme.Etale.mk i.openComplement.ι)))).app K))
          (by rw [← Functor.map_comp]; erw [comp_distTriang_mor_zero₁₂ _ hT]
              exact Functor.map_zero _ _ _)).Exact ∧
        (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.comp_δ _ hT q₀ q₁ h)).Exact ∧
        (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.δ_comp _ hT q₀ q₁ h)).Exact := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_rightDerivedSectionsWithSupport A i K n
  exact ⟨δ, hδ, fun q₀ q₁ h ↦ ⟨DerivedCategory.HomologySequence.exact₂ _ hδ q₀,
    DerivedCategory.HomologySequence.exact₃ _ hδ q₀ q₁ h,
    DerivedCategory.HomologySequence.exact₁ _ hδ q₀ q₁ h⟩⟩

end Concrete

end Etale

end AlgebraicGeometry
