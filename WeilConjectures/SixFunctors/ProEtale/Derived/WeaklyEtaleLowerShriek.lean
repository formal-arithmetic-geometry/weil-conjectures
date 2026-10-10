/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Frobenius
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.WeaklyEtale

/-!
# The derived extension by zero along a weakly étale morphism

Let `g : W ⟶ X` be a weakly étale morphism and let `g_! = ProEtale.localizationLowerShriek`
be the extension by zero, left adjoint to `g^*`. Both functors are exact, so `g_!` induces a
functor `D(g_!)` on derived categories by applying it levelwise. We show:

- `D(g_!)` is left adjoint to the derived pullback `Lg^*`
  (`AlgebraicGeometry.ProEtale.derivedLocalizationLowerShriekAdjunction`);
- **the derived projection formula**: the Frobenius map
  `D(g_!)(Lg^*K ⊗ᴸ M) ⟶ K ⊗ᴸ D(g_!)M` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_frobeniusMap_derivedLocalizationLowerShriekAdjunction`);
- consequently `Lg^*` commutes with derived internal homs: the comparison
  `Lg^* RHom(K, L) ⟶ RHom(Lg^*K, Lg^*L)` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_leftDerivedUpperStar`).

## Implementation notes

The derived adjunction is obtained from the adjunction `g_! ⊣ g^*` on homotopy categories by
localization (`CategoryTheory.Adjunction.localization`), so that its unit is computable on
the images of complexes. The projection formula is reduced, with
`CategoryTheory.Adjunction.isIso_frobeniusMap_obj_of_isIso_frobeniusMap`, first from the
derived categories to the homotopy categories, on a complex `M` such that `M` and `g_! M` are
K-flat (so that the derived tensor products are computed termwise), and then from the
homotopy categories to the categories of complexes, where the Frobenius map is, in each
degree, a sum of the Frobenius isomorphisms of sheaves
(`AlgebraicGeometry.ProEtale.isIso_frobeniusMap_localizationLowerShriekUpperStarAdjunction`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

variable {W X : Scheme.{u}} (g : W ⟶ X) [hg : WeaklyEtale g]

/-! ### The projection formula for complexes -/

/-- The bifunctor `(K, M) ↦ g^*K ⊗ M` on pro-étale sheaves, of type
`Sheaf X ⥤ Sheaf W ⥤ Sheaf W`. -/
noncomputable abbrev upperStarTensor :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology W) A ⥤
      Sheaf (Scheme.ProEt.topology W) A :=
  (((Functor.whiskeringLeft₂ _).obj (g)^*[A]).obj (𝟭 _)).obj (curriedTensor _)

instance : (upperStarTensor A g).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext
    simp

instance (K : Sheaf (Scheme.ProEt.topology X) A) :
    ((upperStarTensor A g).obj K).PreservesZeroMorphisms where
  map_zero _ _ := by simp

/-- The Frobenius maps `g_!(g^*K ⊗ M) ⟶ K ⊗ g_!M` of the adjunction `g_! ⊣ g^*` of sheaves, as
a natural transformation of bifunctors. -/
@[simps]
noncomputable def localizationLowerShriekFrobeniusNatTrans :
    (Functor.postcompose₂.obj (localizationLowerShriek A g hg)).obj (upperStarTensor A g) ⟶
      (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (localizationLowerShriek A g hg)).obj
        (curriedTensor _) where
  app K :=
    { app M := (localizationLowerShriekUpperStarAdjunction A g hg).frobeniusMap K M
      naturality _ _ m :=
        (localizationLowerShriekUpperStarAdjunction A g hg).map_whiskerLeft_comp_frobeniusMap K m }
  naturality _ _ k := NatTrans.ext <| funext fun M ↦
    (localizationLowerShriekUpperStarAdjunction A g hg).map_whiskerRight_comp_frobeniusMap k M

/-- The Frobenius map of the adjunction `g_! ⊣ g^*` on complexes is, in each degree, the
comparison map induced by the Frobenius maps of sheaves. -/
lemma mapHomologicalComplex_frobeniusMap_f
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ)
    (M : CochainComplex (Sheaf (Scheme.ProEt.topology W) A) ℤ) (n : ℤ) :
    (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex
      (.up ℤ)).frobeniusMap K M).f n =
      HomologicalComplex.mapBifunctorComparisonX (localizationLowerShriekFrobeniusNatTrans A g)
        (.up ℤ) K M n := by
  refine HomologicalComplex.mapBifunctor.hom_ext_of_map (localizationLowerShriek A g hg)
    (fun p q h ↦ ?_)
  have hμ : HomologicalComplex.ιTensorObj (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K)
      (((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ) ⋙
        (g)^*[A].mapHomologicalComplex (.up ℤ)).obj M) p q n h ≫
      (Functor.LaxMonoidal.μ ((g)^*[A].mapHomologicalComplex (.up ℤ)) K
        (((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ)).obj M)).f n =
      Functor.LaxMonoidal.μ (g)^*[A] (K.X p)
        ((((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ)).obj M).X q) ≫
        (g)^*[A].map (HomologicalComplex.ιTensorObj K
          (((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ)).obj M) p q n h) := by
    rw [← cancel_mono ((Functor.OplaxMonoidal.δ ((g)^*[A].mapHomologicalComplex (.up ℤ)) K
      (((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ)).obj M)).f n)]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Functor.Monoidal.μ_δ,
      HomologicalComplex.id_f]
    erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX, Category.comp_id]
    exact (Functor.Monoidal.μ_δ_assoc (g)^*[A] (K.X p) _ _).symm
  have e := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (localizationLowerShriekFrobeniusNatTrans A g) (.up ℤ) K M p q n h
  refine Eq.trans ?_ e.symm
  simp only [localizationLowerShriekFrobeniusNatTrans_app_app, Adjunction.frobeniusMap,
    Adjunction.homEquiv_counit, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [HomologicalComplex.Monoidal.ιTensorObj_whiskerLeft_f_assoc
    (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K)
    (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex (.up ℤ)).unit.app M)
    p q n h]
  refine (congrArg (fun t ↦ (localizationLowerShriek A g hg).map
    ((((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K).X p ◁
      (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex
        (.up ℤ)).unit.app M).f q ≫ t) ≫
      (localizationLowerShriekUpperStarAdjunction A g hg).counit.app _) hμ).trans ?_
  simp only [Functor.map_comp, Category.assoc]
  erw [(localizationLowerShriekUpperStarAdjunction A g hg).counit_naturality
    (HomologicalComplex.ιTensorObj K
      (((localizationLowerShriek A g hg).mapHomologicalComplex (.up ℤ)).obj M) p q n h)]
  rfl

/-- **The projection formula for complexes**: the Frobenius map of the adjunction
`g_! ⊣ g^*` on complexes of pro-étale sheaves is an isomorphism. -/
instance isIso_mapHomologicalComplex_frobeniusMap
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ)
    (M : CochainComplex (Sheaf (Scheme.ProEt.topology W) A) ℤ) :
    IsIso (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex
      (.up ℤ)).frobeniusMap K M) := by
  have (n : ℤ) : IsIso ((((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex
      (.up ℤ)).frobeniusMap K M).f n) := by
    rw [mapHomologicalComplex_frobeniusMap_f]
    have (K₀ : Sheaf (Scheme.ProEt.topology X) A) (M₀ : Sheaf (Scheme.ProEt.topology W) A) :
        IsIso (((localizationLowerShriekFrobeniusNatTrans A g).app K₀).app M₀) :=
      inferInstanceAs
        (IsIso ((localizationLowerShriekUpperStarAdjunction A g hg).frobeniusMap K₀ M₀))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The projection formula on homotopy categories**: the Frobenius map of the adjunction
`g_! ⊣ g^*` on homotopy categories of pro-étale sheaves is an isomorphism. It is the image of the
Frobenius map on complexes. -/
instance isIso_mapHomotopyCategory_frobeniusMap
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))
    (M : HomotopyCategory (Sheaf (Scheme.ProEt.topology W) A) (.up ℤ)) :
    IsIso (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomotopyCategory
      (.up ℤ)).frobeniusMap K M) := by
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
  refine ((localizationLowerShriekUpperStarAdjunction A g hg).mapHomologicalComplex
    (.up ℤ)).isIso_frobeniusMap_obj_of_isIso_frobeniusMap
      ((localizationLowerShriekUpperStarAdjunction A g hg).mapHomotopyCategory (.up ℤ))
      ((g)^*[A].mapHomotopyCategoryFactors (.up ℤ)).symm
      ((localizationLowerShriek A g hg).mapHomotopyCategoryFactors (.up ℤ)).symm
      (fun M ↦ ?_) (fun K N ↦ ?_) K M
  · rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    simp [Functor.mapHomotopyCategoryFactors]
  · simp only [Functor.OplaxMonoidal.mapHomotopyCategory_δ,
      Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, Functor.comp_obj, Iso.symm_inv,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
    erw [MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.id_comp]
    have hq (K' N' : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) :
        Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) K' N' = 𝟙 _ := rfl
    have hq' (K' N' : CochainComplex (Sheaf (Scheme.ProEt.topology W) A) ℤ) :
        Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) K' N' = 𝟙 _ := rfl
    rw [hq, hq']
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    rfl

/-! ### The derived adjunction and the derived projection formula -/

variable [Abelian.HasFunctorialFlatResolution A]

/-- The functor `D(g_!)` is induced by `g_!` on homotopy categories. -/
noncomputable instance catCommSqMapDerivedCategoryLocalizationLowerShriek :
    CatCommSq ((localizationLowerShriek A g hg).mapHomotopyCategory (.up ℤ)) Qh Qh
      (localizationLowerShriek A g hg).mapDerivedCategory :=
  ⟨(localizationLowerShriek A g hg).mapDerivedCategoryFactorsh.symm⟩

omit [IsGrothendieckAbelian A] [MonoidalClosed A] hg in
/-- The derived pullback `Lg^*` is induced by `g^*` on homotopy categories, through its
counit. -/
noncomputable instance catCommSqLeftDerivedUpperStar :
    CatCommSq ((g)^*[A].mapHomotopyCategory (.up ℤ)) Qh Qh L((g)^*[A]) :=
  ⟨(asIso (g)^*[A].leftDerivedFunctorCounit).symm⟩

/-- The derived adjunction `D(g_!) ⊣ Lg^*` along a weakly étale morphism `g`: the localization
of the adjunction `g_! ⊣ g^*` on homotopy categories, where the derived functors are compatible
with the localization functors `Qh` through `Functor.mapDerivedCategoryFactorsh` and the counit
of `Lg^*`. -/
noncomputable def derivedLocalizationLowerShriekAdjunction :
    (localizationLowerShriek A g hg).mapDerivedCategory ⊣ L((g)^*[A]) :=
  ((localizationLowerShriekUpperStarAdjunction A g hg).mapHomotopyCategory (.up ℤ)).localization
    Qh (HomotopyCategory.quasiIso _ (.up ℤ)) Qh (HomotopyCategory.quasiIso _ (.up ℤ)) _ _

omit [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)] in
/-- The unit of `derivedLocalizationLowerShriekAdjunction` on the image of a complex. -/
lemma derivedLocalizationLowerShriekAdjunction_unit_app
    (M : HomotopyCategory (Sheaf (Scheme.ProEt.topology W) A) (.up ℤ)) :
    (derivedLocalizationLowerShriekAdjunction A g).unit.app (Qh.obj M) =
      Qh.map (((localizationLowerShriekUpperStarAdjunction A g hg).mapHomotopyCategory
        (.up ℤ)).unit.app M) ≫
        (asIso (g)^*[A].leftDerivedFunctorCounit).inv.app _ ≫
        L((g)^*[A]).map ((localizationLowerShriek A g hg).mapDerivedCategoryFactorsh.inv.app M) :=
  Adjunction.localization_unit_app _ _ _ _ _ _ _ _

/-- Every object of `D(W_proét)` is isomorphic to the image of a K-flat complex `M` such that
`g_! M` is K-flat, namely a functorial flat resolution. -/
lemma exists_kFlat_kFlat_localizationLowerShriek_iso
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology W) A)) :
    ∃ M₀, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M₀ ∧
      (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
        (((localizationLowerShriek A g hg).mapHomotopyCategory (.up ℤ)).obj M₀) ∧
      Nonempty (Qh.obj M₀ ≅ M) := by
  let Λ := (inferInstance :
    HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology W) A)).some.reduced
  obtain ⟨M₁, hM₁⟩ := (Qh.objPreimage M).quotient_obj_surjective
  refine ⟨(HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj M₁),
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M₁),
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((localizationLowerShriek A g hg).kFlat_mapHomologicalComplex_obj_of_colimitsOfShape
        (Λ.colimitOfShapeFlatResolutionFunctorObj
          ObjectProperty.flat.essImage_ι_le M₁).colimitsOfShape),
    ⟨Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ))
      ((HomotopyCategory.quotient _ _).map (Λ.resolutionNatTrans.app M₁)) ?_ ≪≫
        Qh.mapIso (eqToIso hM₁) ≪≫ Qh.objObjPreimageIso M⟩⟩
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  infer_instance

/-- **The derived projection formula** along a weakly étale morphism `g`: the Frobenius map
`D(g_!)(Lg^*K ⊗ᴸ M) ⟶ K ⊗ᴸ D(g_!)M` of `derivedLocalizationLowerShriekAdjunction` is an
isomorphism. By naturality, it suffices to treat the images `K = Qh K₀` and `M = Qh M₀` of
complexes, with `M₀` and `g_! M₀` K-flat. The derived tensor products are then computed
termwise, and the Frobenius map is the image of the Frobenius isomorphism on homotopy
categories. -/
theorem isIso_frobeniusMap_derivedLocalizationLowerShriekAdjunction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology W) A)) :
    letI := monoidalLeftDerivedUpperStar A g
    IsIso ((derivedLocalizationLowerShriekAdjunction A g).frobeniusMap K M) := by
  let := monoidalLeftDerivedUpperStar A g
  obtain ⟨M₀, hM₀, hgM₀, ⟨eM⟩⟩ := exists_kFlat_kFlat_localizationLowerShriek_iso A g M
  have : IsIso (Functor.LaxMonoidal.μ Qh
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj (Qh.objPreimage K)) M₀) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hM₀
  have : IsIso (Functor.LaxMonoidal.μ Qh (Qh.objPreimage K)
      (((localizationLowerShriek A g hg).mapHomotopyCategory (.up ℤ)).obj M₀)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hgM₀
  have : IsIso ((derivedLocalizationLowerShriekAdjunction A g).frobeniusMap
      (Qh.obj (Qh.objPreimage K)) (Qh.obj M₀)) :=
    ((localizationLowerShriekUpperStarAdjunction A g hg).mapHomotopyCategory
      (.up ℤ)).isIso_frobeniusMap_obj_of_isIso_frobeniusMap
        (derivedLocalizationLowerShriekAdjunction A g)
        (asIso (g)^*[A].leftDerivedFunctorCounit).symm
        (localizationLowerShriek A g hg).mapDerivedCategoryFactorsh.symm
        (derivedLocalizationLowerShriekAdjunction_unit_app A g)
        (fun K N ↦ leftDerivedUpperStarTensorComparison_fac A g K N) _ _
  exact (derivedLocalizationLowerShriekAdjunction A g).isIso_frobeniusMap_of_iso
    (Qh.objObjPreimageIso K) eM

/-- **The derived pullback along a weakly étale morphism commutes with internal homs**: the
comparison `Lg^* RHom(K, L) ⟶ RHom(Lg^*K, Lg^*L)` is an isomorphism. This follows from the
derived projection formula
`AlgebraicGeometry.ProEtale.isIso_frobeniusMap_derivedLocalizationLowerShriekAdjunction`. -/
theorem isIso_ihomComparison_leftDerivedUpperStar
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    letI := monoidalLeftDerivedUpperStar A g
    IsIso ((Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).natTrans.app L) := by
  let := monoidalLeftDerivedUpperStar A g
  exact (derivedLocalizationLowerShriekAdjunction A g
    ).isIso_ihomComparison_app_of_isIso_frobeniusMap
    K (isIso_frobeniusMap_derivedLocalizationLowerShriekAdjunction A g K) L
end ProEtale

end AlgebraicGeometry
