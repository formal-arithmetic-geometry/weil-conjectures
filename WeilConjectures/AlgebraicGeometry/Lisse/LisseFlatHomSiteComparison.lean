/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeHomology
import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom

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

private theorem local_assertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K N : Etale.DerivedCategoryModule A X) :
    lisseFlatHomLocalAssertion A X K N := by
  dsimp only [lisseFlatHomLocalAssertion]
  let : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  apply finiteFree_assertion

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed

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

end AlgebraicGeometry.ProEtale
