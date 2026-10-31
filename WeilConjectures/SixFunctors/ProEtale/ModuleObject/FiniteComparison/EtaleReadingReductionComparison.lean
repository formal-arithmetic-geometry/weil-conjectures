/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalarsQuotient
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Left derived functors precomposed with an exact functor preserving flat objects

Let `F : C ⥤ D` be an exact functor between monoidal Grothendieck abelian categories with
functorial flat resolutions, which preserves flat objects and `ℤ`-indexed colimits, and let
`G : D ⥤ E` preserve quasi-isomorphisms between K-flat complexes. Then `D(F) ⋙ LG` is a left
derived functor of `F ⋙ G` (`Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor_of_preservesFlat`):
it is computed on the complexes whose image under `F` is K-flat, which form a left derivability
structure (`Functor.isLeftDerivabilityStructure_kFlatKFlatMap`). Unlike
`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`, this does not need `F` to preserve K-flat
complexes.

This applies to the comparison pullback `ν^*` from étale to pro-étale sheaves, which preserves
flat sheaves.
-/

@[expose] public section

universe u u₁ u₂ u₃

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso] {H : C ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H)

/-- The counit exhibiting `D(F) ⋙ LG` as a candidate left derived functor of
`H.mapHomotopyCategory ⋙ Qh`, for an exact functor `F` and an isomorphism `e : F ⋙ G ≅ H`: it is
assembled from the comparison `F.mapDerivedCategoryFactorsh`, the counit of `LG` and the
isomorphism `K(F) ⋙ K(G) ≅ K(H)` induced by `e`. -/
noncomputable def mapDerivedCategoryCompLeftDerivedFunctorCounit :
    Qh ⋙ (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) ⟶
      H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom G.leftDerivedFunctor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) G.leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom Qh

/-- The counit `mapDerivedCategoryCompLeftDerivedFunctorCounit` is an isomorphism on the
complexes whose image under `F` is K-flat. -/
lemma isIso_mapDerivedCategoryCompLeftDerivedFunctorCounit_app
    (X : HomotopyCategory C (.up ℤ)) (hX : F.kFlatMap X) :
    IsIso ((F.mapDerivedCategoryCompLeftDerivedFunctorCounit G e).app X) := by
  have := G.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hX
  dsimp [mapDerivedCategoryCompLeftDerivedFunctorCounit]
  infer_instance

variable [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

/-- **Left derived functors precomposed with an exact functor preserving flat objects**: for an
exact functor `F` preserving flat objects and `ℤ`-indexed colimits, `G` preserving K-flat
quasi-isomorphisms and `e : F ⋙ G ≅ H`, the functor `D(F) ⋙ LG` is a left derived functor of
`H`, with the counit `mapDerivedCategoryCompLeftDerivedFunctorCounit`. It is computed on the
K-flat complexes whose image under `F` is K-flat. -/
lemma isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor_of_preservesFlat :
    (F.mapDerivedCategory ⋙ G.leftDerivedFunctor).IsLeftDerivedFunctor
      (F.mapDerivedCategoryCompLeftDerivedFunctorCounit G e)
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
  have hα (X : F.kFlatKFlatMap.FullSubcategory) :
      IsIso ((F.mapDerivedCategoryCompLeftDerivedFunctorCounit G e).app
        ((HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap).functor.obj X)) :=
    F.isIso_mapDerivedCategoryCompLeftDerivedFunctorCounit_app G e X.obj X.property.2
  exact (LocalizerMorphism.Derives.of_isIso_app_functor_obj'
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap) _ hα).isLeftDerivedFunctor_of_isIso
      _ hα

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]

/-- An exact faithful functor reflects bounded below objects of the derived categories: if
`D(F) X` is bounded below, so is `X`, the homology of `D(F) X` being `F` of the homology of
`X`. -/
lemma plus_of_plus_mapDerivedCategory_obj {X : DerivedCategory C}
    (hX : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj X)) :
    DerivedCategory.TStructure.t.plus X := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, (DerivedCategory.isGE_iff X n).2 fun i hi ↦ ?_⟩
  have h : IsZero (F.obj ((DerivedCategory.homologyFunctor C i).obj X)) :=
    ((DerivedCategory.isGE_iff _ n).1 hn i hi).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso i).app X)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact F.map_injective (by rw [F.map_id, h, F.map_zero])

end CategoryTheory.Functor

/-! ### The comparison `ν` and the derived extension of scalars -/

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [IsNoetherianRing Λ] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

variable (φ) in
/-- The comparison `ν^*` commutes with the extension of scalars of sheaves:
`ν^*(Λ' ⊗_Λ F) ≅ Λ' ⊗_Λ ν^* F` (`etaleSheafExtendScalarsCompComparisonUpperStarIso`). -/
noncomputable def comparisonUpperStarCompExtendScalarsIso :
    ν^*(X)[ModuleCat.{u + 1} Λ] ⋙ Sheaf.extendScalars (Scheme.ProEt.topology X) φ ≅
      Sheaf.extendScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ'] :=
  (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).symm

/-- The counit exhibiting `D(ν^*) ⋙ (- ⊗ᴸ_Λ Λ')` as a left derived functor of
`F ↦ Λ' ⊗_Λ ν^* F ≅ ν^*(Λ' ⊗_Λ F)` (`Functor.mapDerivedCategoryCompLeftDerivedFunctorCounit`). -/
noncomputable def comparisonUpperStarDerivedExtendScalarsCounit :
    Qh ⋙ (D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙ ProEtale.derivedExtendScalars hφ ha X) ⟶
      (Sheaf.extendScalars X.smallEtaleTopology φ ⋙
        ν^*(X)[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh :=
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  (ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryCompLeftDerivedFunctorCounit
    (Sheaf.extendScalars (Scheme.ProEt.topology X) φ) (comparisonUpperStarCompExtendScalarsIso φ X)

instance isLeftDerivedFunctor_comparisonUpperStar_comp_derivedExtendScalars :
    (D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙ ProEtale.derivedExtendScalars hφ ha X).IsLeftDerivedFunctor
      (comparisonUpperStarDerivedExtendScalarsCounit hφ ha X)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  (ν^*(X)[ModuleCat.{u + 1} Λ]).isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor_of_preservesFlat
    (Sheaf.extendScalars (Scheme.ProEt.topology X) φ) (comparisonUpperStarCompExtendScalarsIso φ X)

/-- The counit exhibiting `(- ⊗ᴸ_Λ Λ') ⋙ D(ν^*)` as a left derived functor of
`F ↦ ν^*(Λ' ⊗_Λ F)` (`Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit`). -/
noncomputable def derivedExtendScalarsComparisonUpperStarCounit :
    Qh ⋙ (Etale.derivedExtendScalars hφ ha X ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ'])) ⟶
      (Sheaf.extendScalars X.smallEtaleTopology φ ⋙
        ν^*(X)[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh :=
  have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
  Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit
    (Sheaf.extendScalars X.smallEtaleTopology φ) (ν^*(X)[ModuleCat.{u + 1} Λ'])

instance isLeftDerivedFunctor_derivedExtendScalars_comp_comparisonUpperStar :
    (Etale.derivedExtendScalars hφ ha X ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ'])).IsLeftDerivedFunctor
      (derivedExtendScalarsComparisonUpperStarCounit hφ ha X)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
  Functor.isLeftDerivedFunctor_leftDerivedFunctor_comp_mapDerivedCategory
    (Sheaf.extendScalars X.smallEtaleTopology φ) (ν^*(X)[ModuleCat.{u + 1} Λ'])

/-- **The comparison `ν^*` commutes with the derived extension of scalars**:
`(ν^* K) ⊗ᴸ_Λ Λ' ≅ ν^*(K ⊗ᴸ_Λ Λ')`, for a surjective `φ : Λ →+* Λ'` with principal kernel. Both
sides are left derived functors of `F ↦ ν^*(Λ' ⊗_Λ F) ≅ Λ' ⊗_Λ ν^* F`
(`etaleSheafExtendScalarsCompComparisonUpperStarIso`): the right one because `ν^*` is exact, the
left one because `ν^*` is exact and preserves flat sheaves
(`Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor_of_preservesFlat`). -/
noncomputable def comparisonUpperStarDerivedExtendScalarsIso :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙ ProEtale.derivedExtendScalars hφ ha X ≅
      Etale.derivedExtendScalars hφ ha X ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ']) :=
  Functor.leftDerivedUnique _ _ (comparisonUpperStarDerivedExtendScalarsCounit hφ ha X)
    (derivedExtendScalarsComparisonUpperStarCounit hφ ha X)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- **The derived extension of scalars commutes with `Rν_*`**: the base change map
`Rν_*(L) ⊗ᴸ_Λ Λ' ⟶ Rν_*(L ⊗ᴸ_Λ Λ')`, the mate under the adjunctions `ν^* ⊣ Rν_*` of the
commutation `comparisonUpperStarDerivedExtendScalarsIso` of `ν^*` with the derived extension of
scalars. It is invertible on objects of étale origin whose extension of scalars is bounded below
(`isIso_derivedExtendScalarsComparisonLowerStarMap_app`). -/
noncomputable def derivedExtendScalarsComparisonLowerStarMap :
    R(ν_*(X)[ModuleCat.{u + 1} Λ]) ⋙ Etale.derivedExtendScalars hφ ha X ⟶
      ProEtale.derivedExtendScalars hφ ha X ⋙ R(ν_*(X)[ModuleCat.{u + 1} Λ']) :=
  mateEquiv (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (TwoSquare.mk _ _ _ _ (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).inv)

/-- The defining property of `derivedExtendScalarsComparisonLowerStarMap`, in terms of the units
of `ν^* ⊣ Rν_*`. -/
@[reassoc]
lemma map_unit_app_comp_derivedExtendScalarsComparisonLowerStarMap_app
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.derivedExtendScalars hφ ha X).map
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app N) ≫
      (derivedExtendScalarsComparisonLowerStarMap hφ ha X).app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj N) =
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X).unit.app
        ((Etale.derivedExtendScalars hφ ha X).obj N) ≫
      R(ν_*(X)[ModuleCat.{u + 1} Λ']).map
        ((comparisonUpperStarDerivedExtendScalarsIso hφ ha X).inv.app N) :=
  unit_mateEquiv _ _ _ N

/-- The base change map `Rν_*(L) ⊗ᴸ_Λ Λ' ⟶ Rν_*(L ⊗ᴸ_Λ Λ')` is an isomorphism at `L = ν^* N` for
`N` bounded below with `N ⊗ᴸ_Λ Λ'` bounded below: the units of `ν^* ⊣ Rν_*` are invertible on
bounded below complexes. -/
lemma isIso_derivedExtendScalarsComparisonLowerStarMap_app_obj
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : DerivedCategory.TStructure.t.plus N)
    (hN' : DerivedCategory.TStructure.t.plus ((Etale.derivedExtendScalars hφ ha X).obj N)) :
    IsIso ((derivedExtendScalarsComparisonLowerStarMap hφ ha X).app
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj N)) := by
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X N hN
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ') X _ hN'
  have h := map_unit_app_comp_derivedExtendScalarsComparisonLowerStarMap_app hφ ha X N
  have : IsIso ((Etale.derivedExtendScalars hφ ha X).map
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app N) ≫
    (derivedExtendScalarsComparisonLowerStarMap hφ ha X).app
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj N)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Etale.derivedExtendScalars hφ ha X).map
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app N)) _

/-- **The base change map `Rν_*(L) ⊗ᴸ_Λ Λ' ⟶ Rν_*(L ⊗ᴸ_Λ Λ')` is an isomorphism** for `L` bounded
below of étale origin such that `L ⊗ᴸ_Λ Λ'` is bounded below. Writing `L ≅ ν^* N`, the complex
`N ⊗ᴸ_Λ Λ'` is bounded below, as `ν^*(N ⊗ᴸ_Λ Λ') ≅ L ⊗ᴸ_Λ Λ'` is and `ν^*` is exact and
faithful. -/
lemma isIso_derivedExtendScalarsComparisonLowerStarMap_app
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X L)
    (hL' : DerivedCategory.TStructure.t.plus ((ProEtale.derivedExtendScalars hφ ha X).obj L)) :
    IsIso ((derivedExtendScalarsComparisonLowerStarMap hφ ha X).app L) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hL
  have hN' : DerivedCategory.TStructure.t.plus ((Etale.derivedExtendScalars hφ ha X).obj N) :=
    (ν^*(X)[ModuleCat.{u + 1} Λ']).plus_of_plus_mapDerivedCategory_obj
      (DerivedCategory.TStructure.t.plus.prop_of_iso
        ((ProEtale.derivedExtendScalars hφ ha X).mapIso e.symm ≪≫
          (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).app N) hL')
  have := isIso_derivedExtendScalarsComparisonLowerStarMap_app_obj hφ ha X N hN hN'
  have h := (derivedExtendScalarsComparisonLowerStarMap hφ ha X).naturality e.hom
  have : IsIso ((R(ν_*(X)[ModuleCat.{u + 1} Λ]) ⋙ Etale.derivedExtendScalars hφ ha X).map e.hom ≫
      (derivedExtendScalarsComparisonLowerStarMap hφ ha X).app L) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((R(ν_*(X)[ModuleCat.{u + 1} Λ]) ⋙ Etale.derivedExtendScalars hφ ha X).map e.hom) _

end AlgebraicGeometry.ProEtale
