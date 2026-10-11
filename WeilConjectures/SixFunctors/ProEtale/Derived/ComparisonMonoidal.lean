/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal

/-!
# The comparison pullback and the derived tensor product

Let `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` be the comparison pullback. We show that it is strong
monoidal, and that the two bifunctors `(K, M) ↦ ν^*K ⊗ᴸ ν^*M` and `(K, M) ↦ ν^*(K ⊗ᴸ M)`, of
type `D(X_ét) ⥤ D(X_ét) ⥤ D(X_proét)`, are isomorphic. This is the counterpart for `ν^*` of
`WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal`, and the proofs are the same:
the oplax monoidal structure of `ν^*` is derived with `CategoryTheory.Functor.leftDerived₂NatIso`,
on pairs of complexes `(K, M)` with `K` K-flat and `ν^*M` K-flat.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.monoidal_comparisonUpperStar`: `ν^*` is strong monoidal.
- `AlgebraicGeometry.ProEtale.kFlatComparisonUpperStar`: the complexes on `X_ét` whose comparison
  pullback is K-flat; they form a left derivability structure when `ν^*` preserves flat objects.
- `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarTensorNatIso`: the natural
  isomorphism `Lν^*(K ⊗ᴸ M) ≅ Lν^*K ⊗ᴸ Lν^*M`.
- `AlgebraicGeometry.ProEtale.mapDerivedCategoryComparisonUpperStarTensorIso`: its form
  `ν^*(K ⊗ᴸ M) ≅ ν^*K ⊗ᴸ ν^*M` for the levelwise functor `D(ν^*)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

namespace ProEtale

variable (X : Scheme.{u})

section Sheaf

open Functor.OplaxMonoidal

/-- The comparison pullback `ν^*` is oplax monoidal, being the pullback of sheaves along the
inclusion of sites. -/
noncomputable instance oplaxMonoidal_comparisonUpperStar : (ν^*(X)[A]).OplaxMonoidal := by
  unfold comparisonUpperStar
  infer_instance

/-- The comma categories of the inclusion `ν : X_ét ⥤ X_proét` are filtered: `ν` is
representably flat. -/
lemma isFiltered_costructuredArrow_toProEt (K : X.ProEtᵒᵖ) :
    IsFiltered (CostructuredArrow (X.toProEt).op K) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (Opposite.unop K))

/-- The comparison map `η : ν^*𝟙 ⟶ 𝟙` is an isomorphism. -/
instance isIso_comparisonUpperStar_η : IsIso (η (ν^*(X)[A])) := by
  have (K : X.ProEtᵒᵖ) : IsConnected (CostructuredArrow (X.toProEt).op K) :=
    have := isFiltered_costructuredArrow_toProEt X K
    IsFiltered.isConnected _
  unfold comparisonUpperStar
  infer_instance

/-- The comparison map `δ : ν^*(F ⊗ G) ⟶ ν^*F ⊗ ν^*G` is an isomorphism. -/
instance isIso_comparisonUpperStar_δ (F G : Sheaf X.smallEtaleTopology A) :
    IsIso (δ (ν^*(X)[A]) F G) := by
  have (K : X.ProEtᵒᵖ) : IsSifted (CostructuredArrow (X.toProEt).op K) :=
    have := isFiltered_costructuredArrow_toProEt X K
    inferInstance
  unfold comparisonUpperStar
  infer_instance

/-- The comparison pullback `ν^*` is strong monoidal, its oplax structure being
`AlgebraicGeometry.ProEtale.oplaxMonoidal_comparisonUpperStar`. -/
noncomputable instance monoidal_comparisonUpperStar : (ν^*(X)[A]).Monoidal :=
  .ofOplaxMonoidal _

end Sheaf

section KFlat

variable [Abelian.HasFunctorialFlatResolution A]

/-- The comparison pullback `ν^*` preserves flat sheaves of modules over a noetherian ring
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`). -/
instance preservesFlat_comparisonUpperStar (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).PreservesFlat :=
  ⟨flat_comparisonUpperStar_obj⟩

omit [Abelian.HasFunctorialFlatResolution A] in
variable {A X} in
/-- If `ν^*` preserves flat sheaves, it sends `ℤ`-indexed colimits of bounded above complexes of
flat sheaves, in particular flat resolutions, to K-flat complexes. -/
lemma kFlat_comparisonUpperStar_mapHomologicalComplex_obj [(ν^*(X)[A]).PreservesFlat]
    {K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ}
    (hK : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ K) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((ν^*(X)[A]).mapHomologicalComplex (.up ℤ)).obj K) :=
  (ν^*(X)[A]).kFlat_mapHomologicalComplex_obj_of_colimitsOfShape hK

/-- The complexes of étale sheaves on `X` whose comparison pullback is K-flat: the inverse image
of the K-flat complexes of `K(X_proét)` under `ν^* : K(X_ét) ⥤ K(X_proét)`. -/
abbrev kFlatComparisonUpperStar :
    ObjectProperty (HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.inverseImage
    ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ))

/-- The comparison pullbacks of the functorial flat resolutions of complexes of étale sheaves are
K-flat. -/
lemma kFlatComparisonUpperStar_quotient_obj_resolutionFunctor_obj
    [(ν^*(X)[A]).PreservesFlat]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf X.smallEtaleTopology A))
    [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    kFlatComparisonUpperStar A X
      ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  ObjectProperty.prop_of_iso
    (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)).kFlat
    (((ν^*(X)[A]).mapHomotopyCategoryFactors (.up ℤ)).app (Λ.resolutionFunctor.obj K)).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_comparisonUpperStar_mapHomologicalComplex_obj
        (Λ.colimitOfShapeFlatResolutionFunctorObj
          ObjectProperty.flat.essImage_ι_le K).colimitsOfShape))

/-- The complexes whose comparison pullback is K-flat form a left derivability structure on
`K(X_ét)` for the quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatComparisonUpperStar [(ν^*(X)[A]).PreservesFlat] :
    (HomotopyCategory.quasiIsoLocalizerMorphism
      (kFlatComparisonUpperStar A X)).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf X.smallEtaleTopology A)).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatComparisonUpperStar_quotient_obj_resolutionFunctor_obj A X Λ.reduced)

end KFlat

section Derived

variable [Abelian.HasFunctorialFlatResolution A]

open _root_.DerivedCategory Functor.LaxMonoidal

/-- The bifunctor `(K, M) ↦ Lν^*K ⊗ᴸ Lν^*M`, of type `D(X_ét) ⥤ D(X_ét) ⥤ D(X_proét)`. -/
noncomputable abbrev derivedTensorLeftDerivedComparisonUpperStar :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (((Functor.whiskeringLeft₂ _).obj L(ν^*(X)[A])).obj L(ν^*(X)[A])).obj
    (ProEtale.derivedTensor A X)

/-- The bifunctor `(K, M) ↦ Lν^*(K ⊗ᴸ M)`, of type `D(X_ét) ⥤ D(X_ét) ⥤ D(X_proét)`. -/
noncomputable abbrev leftDerivedComparisonUpperStarDerivedTensor :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (Functor.postcompose₂.obj L(ν^*(X)[A])).obj (Etale.derivedTensor A X)

/-- The counit exhibiting `(K, M) ↦ Lν^*K ⊗ᴸ Lν^*M` as the total left derived functor of
`(A, B) ↦ ν^*A ⊗ ν^*B`: the counits of `Lν^*` on both factors, followed by the lax monoidal
structure of `Qh : K(X_proét) ⥤ D(X_proét)`. -/
noncomputable def derivedTensorLeftDerivedComparisonUpperStarCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf X.smallEtaleTopology A))).obj Qh).obj
        (derivedTensorLeftDerivedComparisonUpperStar A X) ⟶
      (((Functor.whiskeringLeft₂ _).obj ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ))).obj
        ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ))).obj
          ((Functor.postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((Functor.whiskeringLeft₂ _).map (ν^*(X)[A]).leftDerivedFunctorCounit).app
      (Qh ⋙ L(ν^*(X)[A]))).app (ProEtale.derivedTensor A X) ≫
    (((Functor.whiskeringLeft₂ _).obj ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      (ν^*(X)[A]).leftDerivedFunctorCounit).app (ProEtale.derivedTensor A X) ≫
    (((Functor.whiskeringLeft₂ _).obj ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ))).obj
        ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ))).map (μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ Lν^*(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ ν^*(A ⊗ B)`: `Lν^*` applied to the lax monoidal structure of `Qh`, followed by the
counit of `Lν^*`. -/
noncomputable def leftDerivedComparisonUpperStarDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf X.smallEtaleTopology A))).obj Qh).obj
        (leftDerivedComparisonUpperStarDerivedTensor A X) ⟶
      (Functor.postcompose₂.obj ((ν^*(X)[A]).mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.obj L(ν^*(X)[A])).map (μNatTrans Qh) ≫
    (Functor.postcompose₂.map (ν^*(X)[A]).leftDerivedFunctorCounit).app (curriedTensor _)

/-- `(K, M) ↦ Lν^*K ⊗ᴸ Lν^*M` is the total left derived functor of `(A, B) ↦ ν^*A ⊗ ν^*B`. It is
computed on pairs `(K, M)` with `K` K-flat and `ν^*M` K-flat. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedComparisonUpperStar
    [(ν^*(X)[A]).PreservesFlat] :
    (derivedTensorLeftDerivedComparisonUpperStar A X).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedComparisonUpperStarCounit A X)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatComparisonUpperStar A X)) _
    (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    (((ν^*(X)[A]).mapHomotopyCategory _).obj X₁.obj) _ X₂.property
  simp only [derivedTensorLeftDerivedComparisonUpperStarCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

/-- `(K, M) ↦ Lν^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ ν^*(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
theorem isLeftDerivedFunctor₂_leftDerivedComparisonUpperStar_derivedTensor :
    (leftDerivedComparisonUpperStarDerivedTensor A X).IsLeftDerivedFunctor₂
      (leftDerivedComparisonUpperStarDerivedTensorCounit A X)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := Etale.isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  simp only [leftDerivedComparisonUpperStarDerivedTensorCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso L(ν^*(X)[A]) (((μNatTrans Qh).app X₁.obj).app X₂.obj)) inferInstance

open Functor.OplaxMonoidal in
/-- The natural isomorphism `Lν^*(K ⊗ᴸ M) ≅ Lν^*K ⊗ᴸ Lν^*M` of bifunctors
`D(X_ét) ⥤ D(X_ét) ⥤ D(X_proét)`, obtained by deriving the oplax monoidal structure `δ` of
`ν^*`, which is invertible. -/
noncomputable def leftDerivedComparisonUpperStarTensorNatIso [(ν^*(X)[A]).PreservesFlat] :
    leftDerivedComparisonUpperStarDerivedTensor A X ≅
      derivedTensorLeftDerivedComparisonUpperStar A X :=
  have := isLeftDerivedFunctor₂_derivedTensor_leftDerivedComparisonUpperStar A X
  have := isLeftDerivedFunctor₂_leftDerivedComparisonUpperStar_derivedTensor A X
  Functor.leftDerived₂NatIso _ (derivedTensorLeftDerivedComparisonUpperStarCounit A X)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedComparisonUpperStarDerivedTensorCounit A X)
    (asIso (Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (ν^*(X)[A])) Qh))

variable {X} in
/-- For a fixed `K : D(X_ét)`, the isomorphism `ν^*(K ⊗ᴸ M) ≅ ν^*K ⊗ᴸ ν^*M` of functors of `M`,
for the levelwise functor `D(ν^*)`. -/
noncomputable def derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    [(ν^*(X)[A]).PreservesFlat] (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ D(ν^*(X)[A]) ≅
      D(ν^*(X)[A]) ⋙ (ProEtale.derivedTensor A X).obj (D(ν^*(X)[A]).obj K) :=
  Functor.isoWhiskerLeft _ (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (leftDerivedComparisonUpperStarTensorNatIso A X).app K ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft D(ν^*(X)[A]) ((ProEtale.derivedTensor A X).mapIso
      ((ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.app K))

variable {X} in
/-- The **projection formula for the comparison morphism**:
`RHom(K, Rν_* N) ≅ Rν_* RHom(ν^* K, N)`, naturally in `N : D(X_proét)`. The two sides are right
adjoint to `G ↦ ν^*(K ⊗ᴸ G)` and to `G ↦ ν^*K ⊗ᴸ ν^*G`, which agree because `ν^*` is strong
monoidal. -/
noncomputable def rightDerivedComparisonLowerStarCompDerivedHomIso [(ν^*(X)[A]).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R(ν_*(X)[A]) ⋙ (Etale.derivedHom A X).obj (Opposite.op K) ≅
      (ProEtale.derivedHom A X).obj (Opposite.op (D(ν^*(X)[A]).obj K)) ⋙ R(ν_*(X)[A]) :=
  ((Etale.derivedTensorHomAdjunction A K).comp (derivedComparisonAdjunction A X)).rightAdjointUniq
    (((derivedComparisonAdjunction A X).comp
      (ProEtale.derivedTensorHomAdjunction A (D(ν^*(X)[A]).obj K))).ofNatIsoLeft
        (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).symm)

end Derived

end ProEtale

end AlgebraicGeometry
