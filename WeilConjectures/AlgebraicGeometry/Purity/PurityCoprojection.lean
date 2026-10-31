/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.Pur9Invertible
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportProjectionApplication
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.CategoryTheory.SmoothPurity.RelativeTensorMate
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginTensorFiniteTor
import WeilConjectures.AlgebraicGeometry.SmoothPurity.InvertibleCompactSupportProjection
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-!
# Co-projection for a closed immersion

Source: current blueprint, sec-smooth-purity/sk-lem-coprojection,
lem-pur-coprojection and its five-Hom-bijection proof (blueprint: lem-pur-coprojection).

The isomorphism is specified by the projection/counit equation for its inverse.
This equation identifies the canonical right-adjoint comparison, rather than merely
asserting an isomorphism between its endpoints. The exceptional functor and counit
are the transported etale ones, used only on bounded constructible objects.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem intrinsic_constructible_realization
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (h : Scheme.IsConstructibleProEtaleModuleSheaf X B
      ((finiteCoefficientIntrinsicRealization X B).obj N)) :
    IsConstructible (ULift.{u + 1, u} B) N := by
  let R := finiteCoefficientIntrinsicRealization X B
  have : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X B).1
  let e₀ : R.obj ((Scheme.proEtaleModuleRestriction X B).obj (R.obj N)) ≅ R.obj N :=
    asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (finiteCoefficientIntrinsicScalarMap X B)).counit.app (R.obj N))
  let e : (Scheme.proEtaleModuleRestriction X B).obj (R.obj N) ≅ N := R.preimageIso e₀
  exact isConstructible_of_iso e
    ((Scheme.proEtaleModuleRestriction_constructible_iff X B _).1 h)

private theorem finite_support_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)}) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨a, b, fun i hi ↦ ?_⟩
  by_contra hn
  rcases hi with hi | hi
  · exact (not_lt_of_ge (ha hn)) hi
  · exact (not_lt_of_ge (hb hn)) hi

private theorem fixed_constructible_of_intrinsic
    (P : WeilConjectures.PurityFiniteSetting.{u}) [Finite P.Ring] (W : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient)))
    (h : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos W
        ((finiteCoefficientIntrinsicRealization W P.Ring).mapDerivedCategory.obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) W K := by
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let R := finiteCoefficientIntrinsicRealization W P.Ring
  have : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact W P.Ring).1
  obtain ⟨a, b, hz⟩ := finite_support_interval (R.mapDerivedCategory.obj K) h.1
  have hc (q : ℤ) : IsConstructible P.Coefficient
      ((DerivedCategory.homologyFunctor _ q).obj K) := by
    apply intrinsic_constructible_realization W P.Ring
    rw [Scheme.proEtaleModuleRestriction_constructible_iff]
    exact isConstructible_of_iso
      ((Scheme.proEtaleModuleRestriction W P.Ring).mapIso
        ((R.mapDerivedCategoryHomologyFunctorIso q).symm.app K))
      ((Scheme.proEtaleModuleRestriction_constructible_iff W P.Ring _).1 (h.2 q))
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := fixedDerivedOrigin W P.Coefficient K hc a b
    (fun q hq ↦ R.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (hz q hq))
  refine ⟨K₀, ?_, ⟨e⟩⟩
  obtain ⟨hc₀, a₀, b₀, _, hv₀⟩ := hK₀
  exact ⟨⟨⟨a₀, (DerivedCategory.isGE_iff K₀ a₀).2 fun q hq ↦ hv₀ q (Or.inl hq)⟩,
      ⟨b₀, (DerivedCategory.isLE_iff K₀ b₀).2 fun q hq ↦ hv₀ q (Or.inr hq)⟩⟩,
    fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc₀ q)⟩

private theorem fixed_finiteTor_of_intrinsic
    (P : WeilConjectures.PurityFiniteSetting.{u}) [Finite P.Ring] [Finite P.Coefficient]
    (W : Scheme.{u})
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hN : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos W N) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) W N := by
  obtain ⟨a, b, ht⟩ := hN.2
  exact ⟨fixed_constructible_of_intrinsic P W N hN.1,
    a, b, (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      P.Ring W a b ht.1 N).1 ht⟩

private theorem etale_origin_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K) := by
  obtain ⟨K₀, ⟨a, ha⟩, ⟨e⟩⟩ := h
  have : K₀.IsGE a := ha
  refine ⟨_, ⟨a, (Etale.upperStar (ModuleCat.{u + 1} Λ) f).isGE_mapDerivedCategory_obj K₀ a⟩,
    ⟨?_⟩⟩
  exact ((Etale.upperStar _ f).mapDerivedCategoryCompIso _).symm.app K₀ ≪≫
    (Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm).app K₀ ≪≫
    ((comparisonUpperStar _ Y).mapDerivedCategoryCompIso _).app K₀ ≪≫
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.mapIso e

private theorem tor_pullback
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(upperStar A f).PreservesFlat]
    (a b : ℤ) {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (h : DerivedCategory.torAmplitudeIn A Y a b K) :
    DerivedCategory.torAmplitudeIn A X a b ((upperStar A f).leftDerivedFunctor.obj K) := by
  obtain ⟨C, _, _, hC, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn h
  refine (DerivedCategory.torAmplitudeIn A X a b).prop_of_iso
    (((upperStar A f).mapDerivedCategoryFactors.app C).symm ≪≫
      (upperStar A f).mapDerivedCategory.mapIso e ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun n ↦ ?_)
  exact Functor.PreservesFlat.flat_obj (F := upperStar A f) (hC n)

private theorem normalized_tensor_mate
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (E : C ≌ C) (T : D ⥤ D) [T.Full] [T.Faithful]
    (π : F ⋙ T ≅ E.functor ⋙ F)
    (R S : C) (K : D) (ε : F.obj R ⟶ K) (ε' : F.obj S ⟶ T.obj K)
    (hS : P S) (hER : P (E.functor.obj R))
    (hInv : ∀ A, P A → P (E.inverse.obj A))
    (h : ∀ A, P A → Function.Bijective (fun f : A ⟶ R ↦ F.map f ≫ ε))
    (h' : ∀ A, P A → Function.Bijective (fun f : A ⟶ S ↦ F.map f ≫ ε')) :
    ∃ e : S ≅ E.functor.obj R,
      π.hom.app R ≫ F.map e.inv ≫ ε' = T.map ε := by
  obtain ⟨b, hb⟩ := (h' _ hER).2 (π.inv.app R ≫ T.map ε)
  change F.map b ≫ ε' = π.inv.app R ≫ T.map ε at hb
  have : IsIso b := relativeTensorMate_isIso P F E T π.symm R S K ε ε'
    hS hER hInv h h' b hb
  refine ⟨(asIso b).symm, ?_⟩
  change π.hom.app R ≫ F.map b ≫ ε' = T.map ε
  rw [hb, Iso.hom_inv_id_app_assoc]

private theorem tensor_normalized_mate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (F : C ⥤ D)
    (L M : D) (N N' : C) (evalD : L ⊗ M ≅ 𝟙_ D) (evalC : N ⊗ N' ≅ 𝟙_ C)
    (π : F ⋙ tensorRight L ≅ tensorRight N ⋙ F)
    (R S : C) (K : D) (ε : F.obj R ⟶ K) (ε' : F.obj S ⟶ K ⊗ L)
    (hS : P S) (hER : P (R ⊗ N))
    (hInv : ∀ A, P A → P (A ⊗ N'))
    (h : ∀ A, P A → Function.Bijective (fun f : A ⟶ R ↦ F.map f ≫ ε))
    (h' : ∀ A, P A → Function.Bijective (fun f : A ⟶ S ↦ F.map f ≫ ε')) :
    ∃ e : S ≅ R ⊗ N, π.hom.app R ≫ F.map e.inv ≫ ε' = ((curriedTensor D).map ε).app L := by
  let E := tensorRightEquivalenceOfTensorIso evalC ((β_ N' N) ≪≫ evalC)
  let T := tensorRightEquivalenceOfTensorIso evalD ((β_ M L) ≪≫ evalD)
  exact normalized_tensor_mate P F E T.functor π R S K ε ε' hS hER hInv h h'

private theorem pullback_inverse_nonempty
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (eval : L ⊗ M ≅ 𝟙_ _) :
    Nonempty ((upperStar A f).leftDerivedFunctor.obj L ⊗
      (upperStar A f).leftDerivedFunctor.obj M ≅ 𝟙_ _) := by
  exact ⟨(leftDerivedUpperStarTensorIso A f L M).symm ≪≫
    (upperStar A f).leftDerivedFunctor.mapIso eval ≪≫ leftDerivedUpperStarUnitIso A f⟩

private theorem invertible_projection_exists
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (eval : L ⊗ M ≅ 𝟙_ _) [HasCompactification f] :
    ∃ π : rightDerivedLowerShriek A f ⋙ tensorRight L ≅
      tensorRight ((upperStar A f).leftDerivedFunctor.obj L) ⋙ rightDerivedLowerShriek A f,
      ∀ N, π.hom.app N = ((projectionMap A f).app N).app L := by
  have hπ (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      IsIso (((projectionMap A f).app N).app L) :=
    isIso_projectionMap_of_tensor_inverse A f N L M eval
  exact ⟨NatIso.ofComponents (fun N ↦ asIso (((projectionMap A f).app N).app L))
    (fun g ↦ congrArg (fun η ↦ η.app L) ((projectionMap A f).naturality g)), fun _ ↦ rfl⟩

private theorem geometric_tensor_mate
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (eval : L ⊗ M ≅ 𝟙_ _)
    (P : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    [P.IsClosedUnderIsomorphisms]
    (R S : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (ε : (rightDerivedLowerShriek A f).obj R ⟶ K)
    (ε' : (rightDerivedLowerShriek A f).obj S ⟶ K ⊗ L)
    (hS : P S) (hER : P (R ⊗ (upperStar A f).leftDerivedFunctor.obj L))
    (hInv : ∀ N, P N → P (N ⊗ (upperStar A f).leftDerivedFunctor.obj M))
    (h : ∀ N, P N → Function.Bijective
      (fun g : N ⟶ R ↦ (rightDerivedLowerShriek A f).map g ≫ ε))
    (h' : ∀ N, P N → Function.Bijective
      (fun g : N ⟶ S ↦ (rightDerivedLowerShriek A f).map g ≫ ε')) :
    ∃ e : S ≅ R ⊗ (upperStar A f).leftDerivedFunctor.obj L,
      compactSupportProjectionApplication A f R L ≫
        (rightDerivedLowerShriek A f).map e.inv ≫ ε' = ((derivedTensor A Y).map ε).app L := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology Y) A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology X) A)
  obtain ⟨evalC⟩ := pullback_inverse_nonempty A f L M eval
  obtain ⟨π, hπ⟩ := invertible_projection_exists A f L M eval
  obtain ⟨e, he⟩ := tensor_normalized_mate P (rightDerivedLowerShriek A f) L M
    ((upperStar A f).leftDerivedFunctor.obj L) ((upperStar A f).leftDerivedFunctor.obj M)
    eval evalC π R S K ε ε' hS hER hInv h h'
  refine ⟨e, ?_⟩
  rw [compactSupportProjectionApplication_eq, ← hπ]
  exact he

private theorem fixed_coprojection
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z W : Scheme.{u}} [CompactSpace W] (i : Z ⟶ W) [IsClosedImmersion i]
    (K L M : DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) W L)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) W M)
    (eval : L ⊗ M ≅ 𝟙_ _) :
    ∃ hKplus : DerivedCategory.TStructure.t.plus K,
      ∃ hKL : DerivedCategory.TStructure.t.plus (K ⊗ L),
        ∃ e : (rightDerivedUpperShriek Λ i).obj (K ⊗ L) ≅
          (rightDerivedUpperShriek Λ i).obj K ⊗
            (upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor.obj L,
          compactSupportProjectionApplication (ModuleCat.{u + 1} Λ) i
            ((rightDerivedUpperShriek Λ i).obj K) L ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i).map e.inv ≫
              rightDerivedUpperShriekCounit i (K ⊗ L) hKL =
            ((derivedTensor (ModuleCat.{u + 1} Λ) W).map
              (rightDerivedUpperShriekCounit i K hKplus)).app L := by
  classical
  have pull (N : DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)))
      (hN : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) W N) :
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z (((upperStar (ModuleCat.{u + 1} Λ)
          i).leftDerivedFunctor).obj N) ∧
        ∃ a b : ℤ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b (((upperStar
            (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor).obj N) := by
    refine ⟨?_, ?_⟩
    · exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z).prop_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) i).app N).symm
        (etale_origin_pullback Λ i hN.1.plusEtaleOrigin)
    · obtain ⟨a, b, ht⟩ := hN.2
      exact ⟨a, b, tor_pullback (ModuleCat.{u + 1} Λ) i a b ht⟩
  have hQL := pull L hL
  have hQM := pull M hM
  have hKplus := hK.bounded.1
  have hKL := (plusEtaleOrigin_tensor_of_finiteTor Λ
    hK.plusEtaleOrigin hL.1.plusEtaleOrigin hL.2).plus
  have hR := plusEtaleOrigin_rightDerivedUpperShriek_obj (Λ := Λ) i hKplus
  have hS := plusEtaleOrigin_rightDerivedUpperShriek_obj (Λ := Λ) i hKL
  have hER : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z ((rightDerivedUpperShriek Λ
      i).obj K ⊗ ((upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor).obj L) :=
    plusEtaleOrigin_tensor_of_finiteTor Λ hR hQL.1 hQL.2
  refine ⟨hKplus, hKL, ?_⟩
  exact geometric_tensor_mate (ModuleCat.{u + 1} Λ) i L M eval
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z)
    ((rightDerivedUpperShriek Λ i).obj K) ((rightDerivedUpperShriek Λ i).obj (K ⊗ L)) K
    (rightDerivedUpperShriekCounit i K hKplus) (rightDerivedUpperShriekCounit i (K ⊗ L) hKL)
    hS hER
    (fun N hN ↦ plusEtaleOrigin_tensor_of_finiteTor Λ hN hQM.1 hQM.2)
    (fun _ hN ↦ bijective_rightDerivedLowerShriek_map_comp_counit i hN hKplus)
    (fun _ hN ↦ bijective_rightDerivedLowerShriek_map_comp_counit i hN hKL)

/-- The recorded intrinsic bounded constructibility predicate in fixed-scalar coordinates.
The realization is the canonical constant-scalar equivalence, applied termwise.
Source: blueprint lem-pur-coprojection, K in Dbc (blueprint: lem-pur-coprojection). -/
noncomputable def purityCoprojectionConstructible
    (P : WeilConjectures.PurityFiniteSetting.{u}) (W : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  Scheme.intrinsicFiniteTorsionConstructible
    P.coefficients.l P.extension P.level P.level_pos W
      ((finiteCoefficientIntrinsicRealization W P.Ring).mapDerivedCategory.obj K)

/-- The canonical co-projection is an isomorphism, expressed by its inverse's counit
normalization. For F = Ri_!, G = Ri^!, and Q = Li^*, the equation is
PF(GK,L); F(e.inv); eps(K tensor L) = eps(K) tensor id(L).
Thus e.inv is precisely the exceptional transpose of the inverse projection followed
by the tensor of the exceptional counit. Equivalently e is the right-adjoint comparison
induced by projection with the inverse of L. Its direction is G(K tensor L) to GK tensor QL.
The bounded-below witnesses are conclusions, not assumptions on the input or on an
ambient pro-etale adjunction. The proper-map instance fixes the default compactification
coordinates.
Source: blueprint lem-pur-coprojection, canonical-map paragraph
(blueprint: lem-pur-coprojection). -/
noncomputable def purityCoprojectionProperty
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z W : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (aW : W ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aW] [QuasiCompact aW]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace aW
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i
  let G := rightDerivedUpperShriek P.Coefficient i
  let Q := (upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
  let tensorW := derivedTensor (ModuleCat.{u + 1} P.Coefficient) W
  let tensorZ := derivedTensor (ModuleCat.{u + 1} P.Coefficient) Z
  let KL := (tensorW.obj K).obj L
  ∃ hK : DerivedCategory.TStructure.t.plus K,
    ∃ hKL : DerivedCategory.TStructure.t.plus KL,
      ∃ e : G.obj KL ≅ (tensorZ.obj (G.obj K)).obj (Q.obj L),
        ((projectionMap (ModuleCat.{u + 1} P.Coefficient) i).app (G.obj K)).app L ≫
          F.map e.inv ≫ rightDerivedUpperShriekCounit i KL hKL =
        (tensorW.map (rightDerivedUpperShriekCounit i K hK)).app L

/-- Co-projection for a closed immersion, with an inverse in the finite-Tor constructible
category. Source: current blueprint, sk-lem-coprojection/lem-pur-coprojection.md
(blueprint: lem-pur-coprojection).

Proof:
1. Convert intrinsic constructibility and Tor amplitude to fixed-scalar coordinates.
Exact pullback preserves bounded-below etale origin and the Tor interval. Its tensor
and unit comparisons make QL and QM inverse tensor factors. Finite-Tor tensor preserves
bounded-below etale origin, the domain on which the transported exceptional Hom
bijection is available.
2. The canonical projection at the invertible factor L is an isomorphism: apply the
right-adjoint projection theorem for dualizable objects to the proper part of the
compactification, then compose with the open and pullback-composition isomorphisms.
3. Transpose inverse projection followed by the tensor of the exceptional counit,
obtaining b:GK tensor QL to G(K tensor L). Its transpose is its defining equation.
4. The two exceptional Hom bijections, full faithfulness of tensor by L and QL,
and naturality of projection identify postcomposition by b with a bijection.
Transport test objects along the inverse tensor equivalence. Surjectivity at the
target and injectivity at the source make b invertible.
5. Take the inverse isomorphism and cancel projection in its defining equation.
This gives exactly the counit normalization in purityCoprojectionProperty. -/
theorem purity_coprojection
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))]
    (i : Z ⟶ W) [i.IsOver (Spec (.of P.field.k))] [IsClosedImmersion i]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : purityCoprojectionConstructible P W K)
    (_hL : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos W L)
    (_hInv : ∃ d : TensorInvertibleData (fun B C ↦ B ⊗ C) (𝟙_ _) L,
      WeilConjectures.finiteTorConstructibleProEtaleModule
        P.coefficients.l P.extension P.level P.level_pos W d.inverse) :
    purityCoprojectionProperty P i (W ↘ Spec (.of P.field.k)) K L := by
  classical
  have : Finite (Padic.coefficientExtensionRing
      P.coefficients.l P.extension P.level) :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace
    (W ↘ Spec (.of P.field.k))
  have hKbc := fixed_constructible_of_intrinsic P W K _hK
  have hLc := fixed_finiteTor_of_intrinsic P W L _hL
  let d := Classical.choose _hInv
  have hd := Classical.choose_spec _hInv
  have hMc := fixed_finiteTor_of_intrinsic P W d.inverse hd
  unfold purityCoprojectionProperty
  dsimp only
  simp only [← compactSupportProjectionApplication_eq]
  exact fixed_coprojection P.Coefficient i K L d.inverse hKbc hLc hMc d.iso

end AlgebraicGeometry.ProEtale
