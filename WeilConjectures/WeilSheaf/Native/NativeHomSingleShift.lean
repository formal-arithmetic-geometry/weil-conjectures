/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.KInjectiveNatIso
public import WeilConjectures.WeilSheaf.BifunctorHomShift
public import WeilConjectures.WeilSheaf.DerivedHomSingleResolution
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations

/-!
# The native internal hom out of a shifted sheaf

Let `A` be a pro-étale Weil sheaf on `X`. The native derived internal hom
`RHom(A[-n], -)` of `nativeDerivedClosedComparison` out of the complex `A[-n]`, the sheaf `A`
placed in degree `-n`, is the derived functor of the internal hom `𝓗om(A, -)` followed by the
shift by `-n` (`AlgebraicGeometry.ProEtaleWeilSheaf.nativeHomSingleShiftIso`), as soon as
`𝓗om(A, -)` is isomorphic to an exact functor `T`.

On a K-injective complex `I`, the native internal hom is the product-total hom complex
`Hom(A[-n], I)` (the representative model of the native closed structure), which is
`Hom(A[0], I)[-n]` (`CochainComplex.bifunctorHomShiftIso`), that is `𝓗om(A, I)[-n]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.singleResolutionProjection`); these identifications are
natural in `I`, and K-injective complexes represent every object of the derived category.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CochainComplex

variable {C D E : Type*} [Category C] [Category D] [Category E] [Preadditive C] [Preadditive D]
  [Preadditive E] [HasCountableProducts E] (H : Cᵒᵖ ⥤ D ⥤ E)
  [∀ X, (H.obj X).Additive] [H.Additive]

variable {H} in
/-- The isomorphisms `CochainComplex.bifunctorHomShiftIso` are natural in the second
variable. -/
@[reassoc]
lemma bifunctorHomShiftIso_hom_naturality_right (K : CochainComplex C ℤ)
    {Y Y' : CochainComplex D ℤ} (g : Y ⟶ Y') (a b : ℤ) (h : a + b = 0) :
    (bifunctorHomMapRight (H := H) (K := K) g)⟦b⟧' ≫ (bifunctorHomShiftIso H K Y' a b h).hom =
      (bifunctorHomShiftIso H K Y a b h).hom ≫ bifunctorHomMapRight g := by
  ext m p q hpq
  simp

/-- The hom complex `Y ↦ Hom_H(K, Y)` out of a fixed complex `K`, as a functor. -/
@[simps]
noncomputable def bifunctorHomRightFunctor (K : CochainComplex C ℤ) :
    CochainComplex D ℤ ⥤ CochainComplex E ℤ where
  obj Y := bifunctorHomObj H K Y
  map g := bifunctorHomMapRight g
  map_id _ := bifunctorHomMapRight_id
  map_comp _ _ := bifunctorHomMapRight_comp _ _

/-- The commutation `Hom_H(K⟦a⟧, -) ≅ Hom_H(K, -)⟦b⟧` of the hom complex with the shifts, for
`a + b = 0`, as a natural isomorphism. -/
noncomputable def bifunctorHomRightFunctorShiftIso (K : CochainComplex C ℤ) (a b : ℤ)
    (h : a + b = 0) :
    bifunctorHomRightFunctor H (K⟦a⟧) ≅ bifunctorHomRightFunctor H K ⋙ shiftFunctor _ b :=
  (NatIso.ofComponents (fun Y ↦ bifunctorHomShiftIso H K Y a b h)
    (fun g ↦ bifunctorHomShiftIso_hom_naturality_right K g a b h)).symm

end CochainComplex

namespace AlgebraicGeometry.ProEtaleWeilSheaf

section Representatives

universe a b

variable {𝒜 : Type a} [Category.{b} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]
  [HasDerivedCategory.{b} 𝒜] [Abelian.HasKInjectiveResolutions 𝒜] {H₀ : 𝒜ᵒᵖ ⥤ 𝒜 ⥤ 𝒜}
  [H₀.Additive] [∀ P, (H₀.obj P).Additive]
  {H : (DerivedCategory 𝒜)ᵒᵖ × DerivedCategory 𝒜 ⥤ DerivedCategory 𝒜}

/-- A derived internal hom `H` with product-total representatives, out of a fixed complex `P`:
if the hom complexes `Hom_{H₀}(P, -)` followed by the localization are isomorphic to the
localization followed by a functor `Ψ`, then `H(P, -) ≅ Ψ`. -/
noncomputable def NativeHomRepresentatives.sectRIso (R : NativeHomRepresentatives H₀ H)
    (P : CochainComplex 𝒜 ℤ) (Ψ : DerivedCategory 𝒜 ⥤ DerivedCategory 𝒜)
    (Ξ : CochainComplex.bifunctorHomRightFunctor H₀ P ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ Ψ) :
    Prod.sectR (op (DerivedCategory.Q.obj P)) _ ⋙ H ≅ Ψ :=
  DerivedCategory.isoOfKInjective _ _ (fun I hI ↦ R.model P I hI ≪≫ Ξ.app I)
    (fun I I' hI hI' g ↦ by
      have h := R.naturality P P I I' hI hI' (𝟙 P) g
      rw [CategoryTheory.Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
        Category.id_comp] at h
      simp only [Iso.trans_hom, Iso.app_hom, Functor.comp_map, Prod.sectR_map]
      rw [reassoc_of% h, Category.assoc]
      exact congrArg ((R.model P I hI).hom ≫ ·) (Ξ.hom.naturality g))

end Representatives

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The projections `singleResolutionProjection` are natural in the K-injective complex. -/
@[reassoc]
lemma singleResolutionProjection_naturality (A : ProEtaleWeilSheaf k₀ l X)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := (CochainComplex.singleFunctor _ 0).obj A) g ≫ singleResolutionProjection A I' =
      singleResolutionProjection A I ≫
        ((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [singleResolutionProjection, HomologicalComplex.comp_f,
    CochainComplex.bifunctorHomMapRight_f_π_assoc, Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  exact congrArg (_ ≫ ·) (((ihomBifunctor k₀ l X).map
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (g.f n))

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The hom complex out of `A[0]` is the internal hom `𝓗om(A, -)` applied termwise, naturally:
`singleResolutionProjection` as a natural isomorphism. -/
noncomputable def bifunctorHomRightFunctorSingleIso (A : ProEtaleWeilSheaf k₀ l X) :
    CochainComplex.bifunctorHomRightFunctor (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) ≅
      (ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents
    (fun I ↦ have := singleResolutionProjection_isIso A I; asIso (singleResolutionProjection A I))
    (fun g ↦ singleResolutionProjection_naturality A g)
variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- **The native internal hom out of a shifted sheaf.** If the internal hom `𝓗om(A, -)` out of
a pro-étale Weil sheaf `A` is isomorphic to an exact functor `T`, then the native derived
internal hom `RHom(A[-n], -)` out of `A` placed in degree `-n` is `T` applied termwise followed
by the shift by `-n`. -/
noncomputable def nativeHomSingleShiftIso (A : ProEtaleWeilSheaf k₀ l X) (n : ℤ)
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (τ : ihomFunctor k₀ l X A ≅ T) :
    Prod.sectR (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A⟦n⟧))) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      T.mapDerivedCategory ⋙ shiftFunctor _ (-n) :=
  (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.sectRIso _ _
    (Functor.isoWhiskerRight
        (CochainComplex.bifunctorHomRightFunctorShiftIso _ _ n (-n) (add_neg_cancel n) ≪≫
          Functor.isoWhiskerRight (bifunctorHomRightFunctorSingleIso A ≪≫
            NatIso.mapHomologicalComplex τ _) _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.Q.commShiftIso (-n)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight T.mapDerivedCategoryFactors.symm _ ≪≫
      Functor.associator _ _ _)

end AlgebraicGeometry.ProEtaleWeilSheaf
