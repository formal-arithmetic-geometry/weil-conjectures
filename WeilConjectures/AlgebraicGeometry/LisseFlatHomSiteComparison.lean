/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.SiteHomComparisonThick
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeHomology
import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Site comparison for internal Hom from a flat lisse sheaf

Source: blueprint, lem-weil-finite-duality-site-comparison, proof paragraphs 2--3;
Stacks Tags 00NZ, 08JI, 08JB, 03EO and 095I
(blueprint: lem-sf-lisse-flat-hom-site-comparison).

The finite-coordinate maps are actual evaluation maps at the chosen basis vectors.
Finite products in these additive categories are the finite direct sums in the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
attribute [local instance 20000] isNoetherian_of_finite
attribute [local irreducible] Padic.coefficientExtensionAbsoluteValue
  Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionIdeal
universe u c d v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonoidalClosed

namespace AlgebraicGeometry.ProEtale

/-- Evaluate internal Hom at the images of the specified basis vectors. This is a real
map, with no selected Hom isomorphism. The tensor-unit comparison supplies the vectors
after applying F. Source: Stacks 03EO, 08JI, the degree-zero finite-free computation
(blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomCoordinates
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K M : C) (r : ℕ)
    [HasCoproduct (fun _ : Fin r ↦ 𝟙_ C)]
    [HasProduct (fun _ : Fin r ↦ F.obj M)]
    (e : (∐ fun _ : Fin r ↦ 𝟙_ C) ≅ K) :
    (ihom (F.obj K)).obj (F.obj M) ⟶ ∏ᶜ fun _ : Fin r ↦ F.obj M :=
  Pi.lift fun j ↦
    (MonoidalClosed.pre (Functor.LaxMonoidal.ε F ≫
      F.map (Sigma.ι (fun _ : Fin r ↦ 𝟙_ C) j ≫ e.hom))).app
      (F.obj M) ≫ (MonoidalClosed.unitIsoSelf (F.obj M)).hom

/-- The finite-free description of the very evaluation comparison on a slice. The two
coordinate maps are explicitly prescribed by evaluation, and are asserted invertible.
Thus this asserts a conjugacy to the canonical finite-product comparison, rather than
merely the existence of unrelated isomorphic objects. Quantifying over every basis
includes changes of trivialization. Source: Stacks 08JI, 03EO
(blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomFiniteFreeAssertion
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal]
    [HasFiniteCoproducts C] [HasFiniteProducts C] [HasFiniteProducts D]
    (K M : C)
    (β : F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M)) : Prop :=
  ∀ (r : ℕ) (e : (∐ fun _ : Fin r ↦ 𝟙_ C) ≅ K),
    IsIso (lisseFlatHomCoordinates (𝟭 C) K M r e) ∧
    IsIso (lisseFlatHomCoordinates F K M r e) ∧
    β ≫ lisseFlatHomCoordinates F K M r e =
      F.map (lisseFlatHomCoordinates (𝟭 C) K M r e) ≫
        piComparison F (fun _ : Fin r ↦ M)

/-- Specialize the evaluation-coordinate equation to the canonical site comparison.
Source: Stacks 08JI, 03EO (blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomLocalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K M : Etale.DerivedCategoryModule A X) : Prop :=
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let _ : F.Monoidal := siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  lisseFlatHomFiniteFreeAssertion F K M
    ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app M)

/-- Both-variable naturality, stated with abstract functors so that it does not
unfold the derived tensor structures while checking the equation. The specialization
below supplies exactly the existing evaluation comparison.
Source: Stacks 03EO, naturality of evaluation
(blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomNaturality
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{v} D]
    (H : Cᵒᵖ ⥤ C ⥤ C) (G : Dᵒᵖ ⥤ D ⥤ D) (F : C ⥤ D)
    (β : ∀ K M : C, F.obj ((H.obj (op K)).obj M) ⟶
      (G.obj (op (F.obj K))).obj (F.obj M)) (K N : C) : Prop :=
  ∀ (K' N' : C) (f : K' ⟶ K) (g : N ⟶ N'),
    F.map ((H.map f.op).app N ≫ (H.obj (op K')).map g) ≫ β K' N' =
      β K N ≫ (G.map (F.map f).op).app (F.obj N) ≫
        (G.obj (op (F.obj K'))).map (F.map g)

/-- Full conclusion for the ordinary constant-A module categories. Local restriction
is the existing evaluation-normalized square, on all slices and on iterated slices.
The basis assertion uses the derived image of the degree-zero restricted sheaf.
Source: blueprint comparison proof paragraphs 2--3; Stacks 08JB, 08JI, 095I
(blueprint: lem-sf-lisse-flat-hom-site-comparison). -/
def lisseFlatHomSiteAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Etale.DerivedCategoryModule A X) : Prop :=
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let H := Etale.derivedHom (ModuleCat.{u + 1} A) X
  let G := derivedHom (ModuleCat.{u + 1} A) X
  IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K N) ∧
  lisseFlatHomNaturality H G F
    (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X) K N ∧
  (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀, ∃ r : ℕ,
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (𝒰.f i)).obj L ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (Fin r → A)))) ∧
  (∀ U : X.Etale,
    siteHomRestrictionAssertion (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom X U)
      (siteHomEtaleRestrictionMonoidal A X U) (siteHomProEtaleRestrictionMonoidal A X U)
      K N ∧
    lisseFlatHomLocalAssertion A U.left
      ((siteHomEtaleRestriction A X U).obj K) ((siteHomEtaleRestriction A X U).obj N) ∧
    ∀ V : U.left.Etale,
      siteHomRestrictionAssertion (ModuleCat.{u + 1} A) (siteHomEtaleObjectHom U.left V)
        (siteHomEtaleRestrictionMonoidal A U.left V)
        (siteHomProEtaleRestrictionMonoidal A U.left V)
        ((siteHomEtaleRestriction A X U).obj K) ((siteHomEtaleRestriction A X U).obj N)) ∧
  (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
    ((_root_.DerivedCategory.homologyFunctor _ i).obj ((H.obj (op K)).obj N))) ∧
  (∀ a b : ℤ, (∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj N)) →
    ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj ((H.obj (op K)).obj N))) ∧
  (_root_.DerivedCategory.TStructure.t
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).plus ((H.obj (op K)).obj N)

private theorem homComparison_naturality
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K N : C) :
    lisseFlatHomNaturality internalHom internalHom F
      (fun K N ↦ (Functor.LaxMonoidal.ihomComparison F K).natTrans.app N) K N := by
  intro K' N' f g
  change F.map ((pre f).app N ≫ (ihom K').map g) ≫
    (Functor.LaxMonoidal.ihomComparison F K').natTrans.app N' =
    (Functor.LaxMonoidal.ihomComparison F K).natTrans.app N ≫
      (pre (F.map f)).app (F.obj N) ≫ (ihom (F.obj K')).map (F.map g)
  have h : F.map ((ihom K').map g) ≫
      (Functor.LaxMonoidal.ihomComparison F K').natTrans.app N' =
      (Functor.LaxMonoidal.ihomComparison F K').natTrans.app N ≫
        (ihom (F.obj K')).map (F.map g) :=
    (Functor.LaxMonoidal.ihomComparison F K').natTrans.naturality g
  rw [F.map_comp, Category.assoc, h, ← Category.assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc]

private theorem unit_eval
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C] (M : C) :
    (unitIsoSelf M).hom = (λ_ ((ihom (𝟙_ C)).obj M)).inv ≫
      (ihom.ev (𝟙_ C)).app M := by
  simp [unitIsoSelf, unitNatIso, conjugateIsoEquiv, conjugateEquiv]

private theorem coordinate_comp
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K M T : C} (v : 𝟙_ C ⟶ K) (f : T ⟶ (ihom K).obj M) :
    f ≫ (pre v).app M ≫ (unitIsoSelf M).hom =
      (λ_ T).inv ≫ (v ▷ T) ≫ uncurry f := by
  rw [unit_eval, leftUnitor_inv_naturality_assoc,
    id_tensor_pre_app_comp_ev, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, uncurry_eq]

private theorem coordinates_iso
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [∀ T : C, PreservesFiniteCoproducts (tensorRight T)] {K M : C} {r : ℕ}
    [HasProduct (fun _ : Fin r ↦ M)]
    (v : ∀ _j : Fin r, 𝟙_ C ⟶ K) (h : IsColimit (Cofan.mk K v)) :
    IsIso (Pi.lift fun j ↦ (pre (v j)).app M ≫ (unitIsoSelf M).hom) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  let ht := isColimitCofanMkObjOfIsColimit (tensorRight T) (fun _ : Fin r ↦ 𝟙_ C) v h
  constructor
  · intro a b hab
    apply uncurry_injective
    apply ht.hom_ext
    intro j
    have hj := congrArg (fun f ↦ f ≫ Pi.π (fun _ : Fin r ↦ M) j.as) hab
    change (v j.as ▷ T) ≫ uncurry a = (v j.as ▷ T) ≫ uncurry b
    simpa only [Category.assoc, limit.lift_π, Fan.mk_π_app,
      coordinate_comp, cancel_epi] using hj
  · intro a
    let s := Cofan.mk M (fun j : Fin r ↦ (λ_ T).hom ≫ a ≫ Pi.π _ j)
    refine ⟨curry (ht.desc s), ?_⟩
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, coordinate_comp,
      uncurry_curry]
    change (λ_ T).inv ≫ (v j ▷ T) ≫ ht.desc s = _
    rw [show (v j ▷ T) ≫ ht.desc s = s.inj j from ht.fac s ⟨j⟩]
    simp [s]

private def mapped_basis_colimit
    {C : Type c} [Category.{v} C] [MonoidalCategory C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {K : C} {r : ℕ}
    [HasCoproduct (fun _ : Fin r ↦ 𝟙_ C)] [PreservesFiniteCoproducts F]
    (e : (∐ fun _ : Fin r ↦ 𝟙_ C) ≅ K) :
    IsColimit (Cofan.mk (F.obj K) (fun j : Fin r ↦
      Functor.LaxMonoidal.ε F ≫ F.map (Sigma.ι (fun _ : Fin r ↦ 𝟙_ C) j ≫ e.hom))) := by
  let h : IsColimit (Cofan.mk K (fun j : Fin r ↦ Sigma.ι (fun _ : Fin r ↦ 𝟙_ C) j ≫ e.hom)) :=
    IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext e (fun _ ↦ rfl))
  let h' := isColimitCofanMkObjOfIsColimit F (fun _ : Fin r ↦ 𝟙_ C) _ h
  let α : Discrete.functor (fun _ : Fin r ↦ 𝟙_ D) ≅
      Discrete.functor (fun _ : Fin r ↦ F.obj (𝟙_ C)) :=
    Discrete.natIso (fun _ ↦ Functor.Monoidal.εIso F)
  exact (IsColimit.precomposeHomEquiv α
    (Cofan.mk (F.obj K) (fun j : Fin r ↦ F.map (Sigma.ι (fun _ : Fin r ↦ 𝟙_ C) j ≫ e.hom)))).symm h'

private theorem coordinate_comparison
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.Monoidal] {K M : C} (v : 𝟙_ C ⟶ K) :
    (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M ≫
      (pre (Functor.LaxMonoidal.ε F ≫ F.map v)).app (F.obj M) ≫
        (unitIsoSelf (F.obj M)).hom =
      F.map ((pre v).app M ≫ (unitIsoSelf M).hom) := by
  rw [coordinate_comp, uncurry_eq, Functor.LaxMonoidal.ihomComparison_ev,
    comp_whiskerRight]
  dsimp only [Functor.comp_obj]
  rw [Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc, ← F.map_comp, ← F.map_comp]
  congr 1
  simpa only [Category.id_comp, uncurry_id_eq_ev] using
    (coordinate_comp v (𝟙 ((ihom K).obj M))).symm

private theorem finiteFree_assertion
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [∀ T : C, PreservesFiniteCoproducts (tensorRight T)]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    [∀ T : D, PreservesFiniteCoproducts (tensorRight T)]
    (F : C ⥤ D) [F.Monoidal] [PreservesFiniteCoproducts F]
    [HasFiniteCoproducts C] [HasFiniteProducts C] [HasFiniteProducts D]
    (K M : C) :
    lisseFlatHomFiniteFreeAssertion F K M
      ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app M) := by
  intro r e
  refine ⟨?_, ?_, ?_⟩
  · exact coordinates_iso _ (mapped_basis_colimit (𝟭 C) e)
  · exact coordinates_iso _ (mapped_basis_colimit F e)
  · apply Pi.hom_ext
    intro j
    simp only [lisseFlatHomCoordinates, Category.assoc, limit.lift_π, Fan.mk_π_app,
      piComparison_comp_π, ← F.map_comp]
    erw [Pi.lift_π]
    simpa using coordinate_comparison F (M := M) (Sigma.ι (fun _ : Fin r ↦ 𝟙_ C) j ≫ e.hom)

private theorem finiteFree_cover
    (A : Type (u + 1)) [CommRing A] [Finite A] [IsLocalRing A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    [Scheme.IsFiniteLocallyConstantSheaf L] (hflat : ObjectProperty.flat L) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀, ∃ r : ℕ,
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) (𝒰.f i)).obj L ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A (Fin r → A))) := by
  classical
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := L)
  refine ⟨𝒰, fun i ↦ ?_⟩
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  let G := Etale.upperStar (ModuleCat.{u + 1} A) (𝒰.f i)
  have : (G.obj L).IsConstant (𝒰.X i).smallEtaleTopology :=
    (Scheme.isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) L).1 (h𝒰 i)
  have : Scheme.IsFiniteLocallyConstantSheaf (G.obj L) :=
    Scheme.IsFiniteLocallyConstantSheaf.upperStar _ L
  by_cases hX : IsEmpty (𝒰.X i)
  · refine ⟨0, ⟨IsZero.iso (Scheme.Etale.isZero_sheaf_of_isEmpty _)
      (Scheme.Etale.isZero_sheaf_of_isEmpty _)⟩⟩
  rw [not_isEmpty_iff] at hX
  obtain ⟨M, ⟨eM⟩⟩ := (G.obj L).mem_essImage_of_isConstant
  obtain ⟨hd⟩ := Etale.isDualizable_of_constantSheaf_iso eM
    (Functor.PreservesFlat.flat_obj (F := G) hflat)
  let : HasRightDual M := hd
  have : Module.Finite A M := ModuleCat.finite_of_exactPairing M Mᘁ
  have : ObjectProperty.flat M := ObjectProperty.flat_of_isDualizable ⟨hd⟩
  have : Module.Flat A M := (ModuleCat.flat_iff_flat M).1 this
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  exact ⟨Module.finrank A M, ⟨eM.symm ≪≫
    (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
      (Module.finBasis A M).equivFun.toModuleIso⟩⟩

private theorem hom_preserves_vanishing
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (Q K N : _root_.DerivedCategory C) [ExactPairing Q K]
    (hKt : _root_.DerivedCategory.torAmplitudeIn C 0 0 K) (i : ℤ)
    (hz : IsZero ((_root_.DerivedCategory.homologyFunctor C i).obj N)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor C i).obj ((ihom K).obj N)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory C
  let := BraidedCategory.exactPairing_swap Q K
  have ht : _root_.DerivedCategory.torAmplitudeIn C 0 0 Q := by
    simpa using _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Q) hKt
  exact (_root_.DerivedCategory.isZero_homologyFunctor_tensor_of_torAmplitudeIn
    ht N i hz).of_iso
      ((_root_.DerivedCategory.homologyFunctor C i).mapIso (ihomObjIsoTensor Q K N))

private theorem site_naturality
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    lisseFlatHomNaturality (Etale.derivedHom B X) (derivedHom B X)
      (comparisonUpperStar B X).mapDerivedCategory
      (siteComparisonEvaluationHom B X) K N := by
  let : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
  unfold siteComparisonEvaluationHom
  exact homComparison_naturality _ K N

private theorem site_iso_of_pairing
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (Q K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    [ExactPairing Q K] : IsIso (siteComparisonEvaluationHom B X K N) := by
  let : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
  unfold siteComparisonEvaluationHom
  exact Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing _ Q K N

private theorem bounded_constructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (N : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X N ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X N := by
  constructor
  · rintro ⟨hc, a, b, _, hz⟩
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff N a).2
      (fun q hq ↦ hz q (.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff N b).2 (fun q hq ↦ hz q (.inr hq))⟩⟩,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
        (hc q)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff N a).1 ha q
        (hq.trans_le (min_le_left a b))
    · exact (_root_.DerivedCategory.isLE_iff N b).1 hb q
        ((le_max_right a b).trans_lt hq)

private theorem site_vanishing
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (Q K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    [ExactPairing Q K]
    (hKt : _root_.DerivedCategory.torAmplitudeIn
      (Sheaf X.smallEtaleTopology B) 0 0 K) (i : ℤ)
    (hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj N)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
      (((Etale.derivedHom B X).obj (op K)).obj N)) := by
  exact hom_preserves_vanishing Q K N hKt i hz

private def site_hom_tensor
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (Q K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    [ExactPairing Q K] :
    ((Etale.derivedHom B X).obj (op K)).obj N ≅
      ((Etale.derivedTensor B X).obj Q).obj N :=
  ihomObjIsoTensor Q K N

private theorem site_property_hom
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (Q K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    [ExactPairing Q K]
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology B)))
    [P.IsClosedUnderIsomorphisms]
    (h : P (((Etale.derivedTensor B X).obj N).obj Q)) :
    P (((Etale.derivedHom B X).obj (op K)).obj N) := by
  obtain ⟨flip⟩ := Etale.nonempty_iso_derivedTensor_flip B X
  exact P.prop_of_iso (site_hom_tensor B X Q K N).symm
    (P.prop_of_iso ((flip.app Q).app N).symm h)

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed

private theorem local_assertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K N : Etale.DerivedCategoryModule A X) :
    lisseFlatHomLocalAssertion A X K N := by
  dsimp only [lisseFlatHomLocalAssertion]
  let : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  apply finiteFree_assertion

private theorem localized_pairing
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, HasRightDual (P.X n)] :
    Nonempty (ExactPairing (_root_.DerivedCategory.Q.obj P.rightDual)
      (_root_.DerivedCategory.Q.obj P)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory C
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj_rightDual P a b
  exact ⟨BraidedCategory.exactPairing_swap _ _⟩

private theorem lisse_pairing (A : Type (u + 1)) [CommRing A] [Finite A] {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) [Scheme.IsFiniteLocallyConstantSheaf P]
    (hP : ObjectProperty.flat P) :
    ∃ D, Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X D ∧
      Nonempty (ExactPairing D ((_root_.DerivedCategory.singleFunctor _ 0).obj P)) := by
  let C := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P
  have hCl (n : ℤ) : Scheme.IsFiniteLocallyConstantSheaf (C.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
        (HomologicalComplex.singleObjXSelf _ 0 P).symm
    · exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hCf (n : ℤ) : ObjectProperty.flat (C.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 P).symm hP
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  let _ (n : ℤ) : HasRightDual (C.X n) :=
    { rightDual := (ihom (C.X n)).obj (𝟙_ _)
      exact := letI := Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (C.X n) (hCf n)
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨ep⟩ := localized_pairing C 0 0
  refine ⟨_, Etale.constructibleFiniteTor_Q_obj_of_flat A (CochainComplex.rightDual C) (-0) (-0)
    (fun n ↦ ?_) (fun n ↦ ?_), ⟨@exactPairingCongrRight _ _ _ _ _ _ ep
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app P)⟩⟩
  · -- the dual of a lisse flat sheaf is flat, being dualizable
    exact IsDualizable.flat ⟨@HasRightDual.mk _ _ _ _ (C.X (-n))
      (Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (C.X (-n)) (hCf (-n)))⟩
  · -- and lisse
    have := Etale.isFiniteLocallyConstantSheaf_ihom_unit_of_flat (C.X (-n)) (hCf (-n))
    exact Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf this

private theorem site_assertion
    (A : Type (u + 1)) [CommRing A] [Finite A] [IsLocalRing A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    [Scheme.IsFiniteLocallyConstantSheaf L] (hflat : ObjectProperty.flat L)
    (N : Etale.DerivedCategoryModule A X)
    (hN : Etale.DerivedCategory.isBoundedConstructible A X N) :
    lisseFlatHomSiteAssertion A X L N := by
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  obtain ⟨Q, hQ, ⟨pair⟩⟩ :=
    lisse_pairing A L hflat
  let : ExactPairing Q K := pair
  have hNb := (bounded_constructible_iff A X N).1 hN
  have hT := Etale.boundedConstructible_tensor A X hNb hQ.1 hQ.2
  have hH := site_property_hom (ModuleCat.{u + 1} A) X Q K N
    (Etale.DerivedCategory.boundedConstructible _ X) hT
  refine ⟨site_iso_of_pairing _ X Q K N, site_naturality _ X K N,
    finiteFree_cover A X L hflat, ?_, (bounded_constructible_iff A X _).2 hH |>.1,
    ?_, hH.1.1⟩
  · intro U
    exact ⟨siteHomComparison_restriction A X U K N,
      local_assertion A U.left _ _, fun V ↦
        siteHomComparison_restriction A U.left V _ _⟩
  · intro a b hz i hi
    exact site_vanishing (ModuleCat.{u + 1} A) X Q K N
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat) i (hz i hi)

/-- Comparison for a finite flat lisse source, with naturality, all finite-free local
formulas and sharp constructible cohomological bounds. Flatness here is tensor exactness;
`Etale.flat_iff_forall_flat_sheafFiber_obj` identifies it with the stalkwise hypothesis.
Source: blueprint lem-weil-finite-duality-site-comparison, proof paragraphs 2--3;
Stacks Tags 00NZ, 08JB, 08JI, 03EO and 095I
(blueprint: lem-sf-lisse-flat-hom-site-comparison).

Proof:
1. Trivialize L etale locally by finite module values. On each nonempty member its
value is a geometric stalk, hence flat. Over the finite local coefficient ring it is
finite free by lem-weil-pbc-finite-flat-local-free (00NZ). Empty members and X empty
are harmless.
2. Identify comparison pullback on the etale slices by
lem-pe-comparison-etale-slice-abelian-pullback, applied also to scalar endomorphisms.
Use lem-sf-comparison-pullback-exact and lem-pur-site-restriction-module-adjunction-exact
for derived restriction. The canonical RHom restriction and evaluation transpose
(lem-weil-pbc-ringed-internal-hom-exact-restriction and
lem-weil-pbc-ringed-slice-evaluation-transpose) give the displayed restriction square.
The tensor comparisons are those of lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
3. Good-truncate a representative of N at its cohomological bounds. Apply
lem-sf-hom-comparison-finite-free to A^r[0] and this representative on each slice;
constructibility restricts by prop-constructible-pullback. No Tor bound on N is needed.
4. By lem-weil-pbc-ringed-site-bounded-free-rhom-model and
lem-sc-finite-free-internal-hom-exact, RHom is the tuple complex N^r. Evaluation is
sum a_j x_j; the comparison is the tuple identity. There is no sign in degree zero.
This proves invertibility of both specified coordinate maps and their equation.
5. Uncurry the naturality equation: both sides are the same pulled-back evaluation.
Iterated restriction follows from the coherent comparison pullbacks of
lem-weil-pbc-comparison-pullback and the evaluation restriction equation. Every change
of basis acts by precomposition with its matrix, commuting with the tuple identity.
6. The cone of beta restricts to zero on the trivializing cover. The sheaf axiom
kills each cohomology sheaf of that cone, also on the empty scheme. The distinguished
cone criterion lem-kun-distinguished-cone-zero proves beta invertible.
7. The dual D=Hom(L,A) is finite locally constant. Hom(L,-) is exact, checked on the
finite-free cover. Evaluation D tensor G -> Hom(L,G) is an isomorphism for every G by
lem-pc-sheaf-modules-tensor-closed and the same coordinate calculation.
8. A K-injective resolution therefore computes H^i RHom(L,N) as D tensor H^i(N).
Use lem-fd-constructible-tensor-refinement-witness for constructibility and tensor
exactness for the unchanged vanishing interval. This also proves boundedness below. -/
theorem lisseFlatHomSiteComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) (S : Scheme.{u})
    [S.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of D.k))]
    (L : Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))
    [Scheme.IsFiniteLocallyConstantSheaf L] (_hflat : ObjectProperty.flat L)
    (N : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) S)
    (_hN : @Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n n.property) S N) :
    @lisseFlatHomSiteAssertion (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n n.property) S L N := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.property
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (by
      unfold Padic.coefficientExtensionAbsoluteValue
      exact spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers l E) := by
    unfold Padic.coefficientExtensionIntegers
    exact h.2.2.2.1
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := by
    unfold Padic.coefficientExtensionMaximalIdeal Padic.coefficientExtensionIntegers
    exact h.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    by
      unfold Padic.coefficientExtensionUniformizer Padic.coefficientExtensionMaximalIdeal
        Padic.coefficientExtensionIntegers
      exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hle : Padic.coefficientExtensionIdeal l E n ≤
      Padic.coefficientExtensionMaximalIdeal l E := by
    unfold Padic.coefficientExtensionIdeal
    rw [hgen]
    exact Ideal.pow_le_self (Nat.ne_of_gt n.pos)
  let : Nontrivial (Padic.coefficientExtensionRing l E n) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hm.ne_top hle)
  let : IsLocalRing (Padic.coefficientExtensionRing l E n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
      Ideal.Quotient.mk_surjective
  exact site_assertion _ S L _hflat N _hN

end AlgebraicGeometry.ProEtale
