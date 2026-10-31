/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant
import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverSetFLC
import WeilConjectures.SixFunctors.ProEtale.Comparison.Linear
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparisonLocal
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.CocontinuousGenerator

/-! # Simultaneous completed-linear trivialization

Source: latest blueprint, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-system-completed-trivialization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme
open AdicCoefficients

private theorem fixed_scalar_cover (Y : Scheme.{u}) [IsNoetherian Y] [ConnectedSpace Y]
    {A : Type (u + 1)} [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y), WeaklyEtale f ∧ Function.Surjective f.base ∧ QuasiCompact f ∧
      Nonempty (H ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) f ≅
          H ⋙ (pointSmallEtale y).sheafFiber ⋙
            constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) := by
  let U := universalCovers Y Ω
  let a : Ω ≃+* AlgebraicClosure Ω := RingEquiv.ofBijective
    (algebraMap Ω (AlgebraicClosure Ω)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let s := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let y' := s.hom ≫ y
  refine ⟨U.cover y', U.proj y', U.weaklyEtale_proj y', U.surjective_proj y',
    U.quasiCompact_proj y', ⟨?_⟩⟩
  let e := U.towerComparisonUpperStarIsoConstantSheaf' y' A H hH
  rw [U.pt_proj] at e
  exact e ≪≫ Functor.isoWhiskerLeft H
    (Functor.isoWhiskerRight
      (GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleCongr s y))
      (constantSheaf (ProEt.topology (U.cover y')) (ModuleCat.{u + 1} A)))

private theorem singleton_cover_of_surjective (Y : Scheme.{u})
    (X : Scheme.{u}) (f : X ⟶ Y) [WeaklyEtale f] [QuasiCompact f] [Surjective f] :
    ∃ g : ProEt.mk f ⟶ ⊤_ Y.ProEt,
      Sieve.generate (Presieve.singleton g) ∈ ProEt.topology Y (⊤_ Y.ProEt) := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let e : T ≅ ⊤_ Y.ProEt :=
    (MorphismProperty.Over.mkIdTerminal _ Y).uniqueUpToIso terminalIsTerminal
  let k : ProEt.mk f ⟶ T := MorphismProperty.Over.homMk f (by
    change f ≫ 𝟙 Y = f
    exact Category.comp_id f)
  have hk : Sieve.generate (Presieve.singleton k) ∈ ProEt.topology Y T := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton f ∈ proetalePrecoverage Y
    exact Scheme.Hom.singleton_mem_propQCPrecoverage
      (show WeaklyEtale f from inferInstance)
  refine ⟨k ≫ e.hom, (ProEt.topology Y).superset_covering ?_
    ((ProEt.topology Y).pullback_stable e.inv hk)⟩
  rintro Z h ⟨W, a, b, hb, hfact⟩
  cases hb
  refine ⟨_, a, k ≫ e.hom, Presieve.singleton.mk, ?_⟩
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun t ↦ t ≫ e.hom) hfact


private theorem fixed_scalar_cover_object (Y : Scheme.{u})
    [IsNoetherian Y] [ConnectedSpace Y] {A : Type (u + 1)} [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    ∃ (V : Y.ProEt) (g : V ⟶ ⊤_ Y.ProEt),
      Sieve.generate (Presieve.singleton g) ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      Nonempty (H ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) V.hom ≅
          H ⋙ (pointSmallEtale y).sheafFiber ⋙
            constantSheaf (ProEt.topology V.left) (ModuleCat.{u + 1} A)) := by
  obtain ⟨X, f, hf, hs, hq, ⟨e⟩⟩ := fixed_scalar_cover Y Ω y H hH
  let : WeaklyEtale f := hf
  let : Surjective f := ⟨hs⟩
  let : QuasiCompact f := hq
  obtain ⟨g, hg⟩ := singleton_cover_of_surjective Y X f
  exact ⟨ProEt.mk f, g, hg, ⟨e⟩⟩


private theorem quotient_scalar_linearity
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) (q : S ⟶ T)
    [Presheaf.IsLocallySurjective J (a ≫ q).hom]
    (M N : SheafOfModules.{u + 1} S)
    (g : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (hM : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : M.val.obj U, b • x = 0)
    (hN : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : N.val.obj U, b • x = 0)
    (U : Cᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    g.val.app U (b • x) = b • (show N.val.obj U from g.val.app U x) := by
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J (a ≫ q).hom
    (q.hom.app U b))
  rintro W f ⟨r, hr⟩
  have hb : q.hom.app (op W) (S.obj.map f.op b - a.hom.app (op W) r) = 0 := by
    rw [map_sub, NatTrans.naturality_apply q.hom]
    exact sub_eq_zero.mpr hr.symm
  have hMb : ∀ z : M.val.obj (op W),
      S.obj.map f.op b • z = a.hom.app (op W) r • z := by
    intro z
    exact sub_eq_zero.mp ((sub_smul _ _ z).symm.trans (hM _ _ hb z))
  have hNb : ∀ z : N.val.obj (op W),
      S.obj.map f.op b • z = a.hom.app (op W) r • z := by
    intro z
    exact sub_eq_zero.mp ((sub_smul _ _ z).symm.trans (hN _ _ hb z))
  change N.val.map f.op (g.val.app U (b • x)) =
    N.val.map f.op (b • (show N.val.obj U from g.val.app U x))
  have hg (z : M.val.obj U) :
      g.val.app (op W) (M.val.map f.op z) = N.val.map f.op (g.val.app U z) :=
    PresheafOfModules.naturality_apply g.val f.op z
  rw [← hg, N.val.map_smul, M.val.map_smul, hMb, hNb, ← hg]
  exact (g.val.app (op W)).hom.map_smul r (M.val.map f.op x)

private theorem scalar_zero_of_iso
    {A : Type*} [Semiring A] {C : Type*} [Category* C] [Preadditive C] [Linear A C]
    {X Y : C} (e : X ≅ Y) (r : A) (h : r • 𝟙 Y = 0) : r • 𝟙 X = 0 := by
  apply (cancel_mono e.hom).mp
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
    zero_comp, comp_zero] using congrArg (fun f ↦ e.hom ≫ f) h

private theorem completed_quotient_locallySurjective (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology Y)
      (((adicLisseForget Y).map (CompletedConstantReduction.base Y I) ≫
        (adicLisseForget Y).map (limit.π (adicLisseRingSystem Y I) (op n))).hom) := by
  let J := ProEt.topology Y
  let f := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))
  have hs : Presheaf.IsLocallySurjective J ((Functor.const Y.ProEtᵒᵖ).map f) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun U ↦ Ideal.Quotient.mk_surjective)
  have hss : Sheaf.IsLocallySurjective ((constantSheaf J CommRingCat.{u + 1}).map f) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).mpr hs
  have hc : CompletedConstantReduction.base Y I ≫
      limit.π (adicLisseRingSystem Y I) (op n) =
        (constantSheaf J CommRingCat.{u + 1}).map f := by
    simpa [CompletedConstantReduction.base, f, J] using
      (CompletedConstantReduction.base_exists Y I).choose_spec.1 n
  rw [← Functor.map_comp, hc]
  constructor
  intro U x
  exact Presheaf.imageSieve_mem J ((constantSheaf J CommRingCat.{u + 1}).map f).hom x

private theorem completed_kernel_kills (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (π : A) (n : ℕ)
    (M : SheafOfModules.{u + 1} ((adicLisseForget Y).obj
      (adicLisseCompletedRing Y (Ideal.span {π}))))
    (hM : ∀ (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
      (CompletedConstantReduction.base Y (Ideal.span {π})).hom.app U
        ((adicLisseConstantUnit Y A).app U (π ^ (n + 1))) • x = 0)
    (U : Y.ProEtᵒᵖ) (b : (adicLisseCompletedRing Y (Ideal.span {π})).obj.obj U)
    (hb : (limit.π (adicLisseRingSystem Y (Ideal.span {π})) (op n)).hom.app U b = 0)
    (x : M.val.obj U) : b • x = 0 := by
  let I := Ideal.span ({π} : Set A)
  have hc (m : ℕ) : CompletedConstantReduction.base Y I ≫
      (Iso.refl (adicLisseCompletedRing Y I)).inv ≫
        limit.π (adicLisseRingSystem Y I) (op m) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) := by
    simpa [CompletedConstantReduction.base] using
      (CompletedConstantReduction.base_exists Y I).choose_spec.1 m
  have hk := (CompletedConstantAlgebra.projection_surjective_and_kernel Y I
    (Iso.refl _) (CompletedConstantReduction.base Y I) hc n (Iso.refl _)
    (limit.π (adicLisseRingSystem Y I) (op n))
    (by exact (Category.comp_id _).symm) U).2
  apply hk (M.val.obj U) (LinearMap.toSpanSingleton _ _ x) _ b hb
  intro a
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp
    (show (a : A) ∈ Ideal.span ({π ^ (n + 1)} : Set A) from
      (Ideal.span_singleton_pow π (n + 1)) ▸ a.property)
  change (CompletedConstantReduction.base Y I).hom.app U
    ((adicLisseConstantUnit Y A).app U (a : A)) • x = 0
  rw [← hr, map_mul, map_mul, mul_smul, hM U x, smul_zero]

private def quotient_scalar_hom
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) (q : S ⟶ T)
    [Presheaf.IsLocallySurjective J (a ≫ q).hom]
    (M N : SheafOfModules.{u + 1} S)
    (g : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (hM : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : M.val.obj U, b • x = 0)
    (hN : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : N.val.obj U, b • x = 0) : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf R.obj).map g.val)
    (quotient_scalar_linearity a q M N g hM hN)⟩

private def quotient_scalar_iso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) (q : S ⟶ T)
    [Presheaf.IsLocallySurjective J (a ≫ q).hom]
    (M N : SheafOfModules.{u + 1} S)
    (e : (SheafOfModules.restrictScalars a).obj M ≅
      (SheafOfModules.restrictScalars a).obj N)
    (hM : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : M.val.obj U, b • x = 0)
    (hN : ∀ (U : Cᵒᵖ) (b : S.obj.obj U), q.hom.app U b = 0 →
      ∀ x : N.val.obj U, b • x = 0) : M ≅ N where
  hom := quotient_scalar_hom a q M N e.hom hM hN
  inv := quotient_scalar_hom a q N M e.inv hN hM
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f ↦ f.val.app U x) e.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f ↦ f.val.app U x) e.inv_hom_id

private def fixed_scalar_slice_iso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (V : Y.ProEt)
    (F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (N : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (e : F ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) V.hom ≅
      N ⋙ constantSheaf (ProEt.topology V.left) (ModuleCat.{u + 1} A)) :
    F ⋙ (ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V ≅
      (N ⋙ constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) ⋙
        (ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V := by
  let D := ModuleCat.{u + 1} A
  let G := MorphismProperty.Over.map (f := V.hom) ⊤ V.prop
  have : G.IsContinuous (ProEt.topology V.left) (ProEt.topology Y) :=
    ProEt.isContinuous_overMap V.prop
  have : G.IsCocontinuous (ProEt.topology V.left) (ProEt.topology Y) :=
    ProEt.isCocontinuous_overMap V.prop
  let loc := ProEtale.localizationRestriction D V.hom V.prop
  let c : constantSheaf (ProEt.topology Y) D ⋙ loc ≅
      constantSheaf (ProEt.topology V.left) D :=
    Functor.isoWhiskerLeft (Functor.const Y.ProEtᵒᵖ)
      (G.pushforwardContinuousSheafificationCompatibility D
        (ProEt.topology V.left) (ProEt.topology Y)).symm ≪≫
      Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso V.left.ProEtᵒᵖ G.op)
        (presheafToSheaf (ProEt.topology V.left) D)
  let e' : F ⋙ loc ≅ (N ⋙ constantSheaf (ProEt.topology Y) D) ⋙ loc :=
    (Functor.isoWhiskerLeft F
      (ProEtale.upperStarIsoLocalizationRestriction D V.hom V.prop)).symm ≪≫
      e ≪≫ (Functor.isoWhiskerLeft N c).symm
  let L := ProEt.overToLocalization V
  let P := (Functor.whiskeringLeft (Over V)ᵒᵖ V.left.ProEtᵒᵖ D).obj L.op
  let d : loc ⋙ sheafToPresheaf (ProEt.topology V.left) D ⋙ P ≅
      (ProEt.topology Y).overPullback D V ⋙
        sheafToPresheaf ((ProEt.topology Y).over V) D :=
    Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology Y) D)
      ((Functor.whiskeringLeft (Over V)ᵒᵖ Y.ProEtᵒᵖ D).mapIso
        (NatIso.op (ProEt.overToLocalizationCompOverMapIso V)).symm)
  exact ((fullyFaithfulSheafToPresheaf ((ProEt.topology Y).over V) D).whiskeringRight
    ℕᵒᵖ).preimageIso
      ((Functor.isoWhiskerLeft F d).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight e' (sheafToPresheaf (ProEt.topology V.left) D)) P ≪≫
        Functor.isoWhiskerLeft (N ⋙ constantSheaf (ProEt.topology Y) D) d)

section TorsionUnit
open AdicCoefficients CompletedConstantReduction

private theorem constant_preserves_colimits (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    PreservesColimitsOfSize.{u + 1, u + 1} (adicLisseConstantModules Y A) := by
  let P : ModuleCat.{u + 1} A ⥤
      PresheafOfModules.{u + 1} ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const Y.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  have : PreservesColimitsOfSize.{u + 1, u + 1} P := by
    constructor
    intro K _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact comp_preservesColimits P
    (PresheafOfModules.sheafification (adicLisseConstantUnit Y A))

private theorem restriction_preserves_colimits (Y : Scheme.{u})
    {R S : Sheaf (ProEt.topology Y) RingCat.{u + 1}} (f : R ⟶ S) :
    PreservesColimitsOfSize.{u + 1, u + 1} (SheafOfModules.restrictScalars.{u + 1} f) := by
  constructor
  intro K _
  have : ReflectsColimitsOfShape K (SheafOfModules.toSheaf.{u + 1} R) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape K
      (SheafOfModules.restrictScalars.{u + 1} f ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesColimitsOfShape K (SheafOfModules.toSheaf S))
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (SheafOfModules.restrictScalars f) (SheafOfModules.toSheaf R)

private theorem quotient_unit_isIso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    IsIso (((ordinaryAdjunction_exists Y (base Y I)).choose.unit).app
      ((adicLisseConstantModules Y A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))) := by
  let Q := A ⧸ I ^ (n + 1)
  let c := base Y I
  let K := adicLisseConstantModules Y A
  let a := (ordinaryAdjunction_exists Y c).choose
  let P : PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A)) :=
    (siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const Y.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).obj
          (ModuleCat.of A Q)
  let N := (reductionRestrict Y c).obj (CompletedConstantReduction.residue Y I n)
  let r := reduction Y I n
  let g : K.obj (ModuleCat.of A Q) ⟶ N := a.homEquiv _ _ r
  let seed := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit Y A) (P := P) (F := N) g
  have hg (U : Y.ProEtᵒᵖ) (x : Q) :
      seed.app U x = (adicLisseConstantUnit Y Q).app U x := by
    change g.val.app U ((toSheafify (ProEt.topology Y) P.presheaf).app U x) = _
    have ha := (ordinaryAdjunction_exists Y c).choose_spec
      (K.obj (ModuleCat.of A Q)) (CompletedConstantReduction.residue Y I n) r U
      ((toSheafify (ProEt.topology Y) P.presheaf).app U x)
    have hr := (reduction_exists Y I n).choose_spec.1 U 1 x
    refine (eq_of_heq ha).trans ?_
    simp only [map_one, id_eq, one_mul] at hr
    convert hr using 1 <;> rfl
  have hli : Presheaf.IsLocallyInjective (ProEt.topology Y)
      ((PresheafOfModules.toPresheaf _).map seed) := by
    constructor
    intro U x y hxy
    exact Presheaf.equalizerSieve_mem (ProEt.topology Y)
      (toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of Q))) x y
      ((hg U x).symm.trans (hxy.trans (hg U y)))
  have hls : Presheaf.IsLocallySurjective (ProEt.topology Y)
      ((PresheafOfModules.toPresheaf _).map seed) := by
    constructor
    intro U x
    apply (ProEt.topology Y).superset_covering ?_
      (Presheaf.imageSieve_mem (ProEt.topology Y)
        (toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of Q))) x)
    rintro W f ⟨z, hz⟩
    exact ⟨z, (hg _ z).trans hz⟩
  have hW : (ProEt.topology Y).W ((PresheafOfModules.toPresheaf _).map seed) :=
    (ProEt.topology Y).W_of_isLocallyBijective _
  have hgi : IsIso g := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
    have he : g = (PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit Y A) (P := P) (F := N)).symm seed :=
      ((PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit Y A) (P := P) (F := N)).symm_apply_apply g).symm
    rw [he, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    have : IsIso ((presheafToSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).map
        ((PresheafOfModules.toPresheaf _).map seed)) := by
      rw [(ProEt.topology Y).W_eq_inverseImage_isomorphisms] at hW
      exact hW
    exact IsIso.comp_isIso' this (isIso_sheafificationAdjunction_counit
      (J := ProEt.topology Y) (D := AddCommGrpCat.{u + 1})
      ((SheafOfModules.toSheaf _).obj N))
  have hri : IsIso r := (completed_constant_sheaf_reduction Y I).2.1 n
  have he : a.unit.app (K.obj (ModuleCat.of A Q)) ≫
      (reductionRestrict Y c).map r = g := by
    exact (Adjunction.homEquiv_unit a _ _ r).symm
  have : IsIso (a.unit.app (K.obj (ModuleCat.of A Q)) ≫
      (reductionRestrict Y c).map r) := he ▸ hgi
  exact IsIso.of_isIso_comp_right _ ((reductionRestrict Y c).map r)

private theorem quotient_module_unit_isIso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (N : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1))) :
    IsIso (((ordinaryAdjunction_exists Y (base Y I)).choose.unit).app
      ((adicLisseConstantModules Y A).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj N))) := by
  let F := ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1)))
  let K := adicLisseConstantModules Y A
  let a := (ordinaryAdjunction_exists Y (base Y I)).choose
  have : PreservesColimitsOfSize.{u + 1, u + 1} F := by
    constructor
    intro L _
    constructor
    intro G
    infer_instance
  have : PreservesColimitsOfSize.{u + 1, u + 1} K := constant_preserves_colimits Y A
  have : PreservesColimitsOfSize.{u + 1, u + 1} (reductionChange Y (base Y I)) :=
    a.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1} (reductionRestrict Y (base Y I)) :=
    restriction_preserves_colimits Y ((adicLisseForget Y).map (base Y I))
  let α := Functor.whiskerLeft (F ⋙ K) a.unit
  have hi : IsIso (α.app (ModuleCat.of (A ⧸ I ^ (n + 1)) (A ⧸ I ^ (n + 1)))) :=
    quotient_unit_isIso Y I n
  exact ModuleCat.isIso_app_of_rankOne α hi N

private theorem torsion_module_unit_isIso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (N : ModuleCat.{u + 1} A) (hN : Module.IsTorsionBySet A N (↑(I ^ (n + 1)) : Set A)) :
    IsIso (((ordinaryAdjunction_exists Y (base Y I)).choose.unit).app
      ((adicLisseConstantModules Y A).obj N)) := by
  let := hN.module
  let N' := ModuleCat.of (A ⧸ I ^ (n + 1)) N
  let F := ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1)))
  let e : F.obj N' ≅ N := LinearEquiv.toModuleIso
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (NatTrans.isIso_app_iff_of_iso
    (ordinaryAdjunction_exists Y (base Y I)).choose.unit
    ((adicLisseConstantModules Y A).mapIso e)).mp (quotient_module_unit_isIso Y I n N')

end TorsionUnit

private theorem constant_scalar_unit (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A)) ≫
        ((constantCommuteCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)).inv.hom =
      adicLisseConstantUnit Y A := by
  let J := ProEt.topology Y
  let s := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)
  have h : adicLisseConstantUnit Y A ≫ s.hom.hom =
      toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A)) :=
    realizationRingIso_fac J A
  rw [← h, Category.assoc]
  change adicLisseConstantUnit Y A ≫ (s.hom ≫ s.inv).hom = _
  rw [s.hom_inv_id]
  exact Category.comp_id _

private def constant_restriction_iso (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.restrictScalars
      ((constantCommuteCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)).inv ⋙
        constantRingModuleRestriction (ProEt.topology Y) A ≅
      ProFiniteModels.restriction (ProEt.topology Y) A (adicLisseRing Y A)
        (adicLisseConstantUnit Y A) := by
  let R := adicLisseRing Y A
  let s := (constantCommuteCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)
  have h (U : Y.ProEtᵒᵖ) (a : A) :
      s.inv.hom.app U
        ((toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A))).app U a) =
        (adicLisseConstantUnit Y A).app U a :=
    congrArg (fun f ↦ f.app U a) (constant_scalar_unit Y A)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let f : (SheafOfModules.restrictScalars s.inv ⋙
        constantRingModuleRestriction (ProEt.topology Y) A).obj M ⟶
        (ProFiniteModels.restriction (ProEt.topology Y) A R
          (adicLisseConstantUnit Y A)).obj M :=
      ⟨{ app U := ModuleCat.ofHom
           (X := ((SheafOfModules.restrictScalars s.inv ⋙
             constantRingModuleRestriction (ProEt.topology Y) A).obj M).obj.obj U)
           (Y := ((ProFiniteModels.restriction (ProEt.topology Y) A R
             (adicLisseConstantUnit Y A)).obj M).obj.obj U)
           { toFun := id
             map_add' := fun _ _ ↦ rfl
             map_smul' := fun a x ↦ by
               change s.inv.hom.app U
                 ((toSheafify (ProEt.topology Y)
                   ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A))).app U a) •
                     (show M.val.obj U from x) =
                   (adicLisseConstantUnit Y A).app U a • (show M.val.obj U from x)
               rw [h] }
         naturality _ _ _ := by ext x; rfl }⟩
    have : IsIso f := by
      have : ∀ U, IsIso (f.hom.app U) := fun U ↦
        (ConcreteCategory.isIso_iff_bijective (f.hom.app U)).mpr Function.bijective_id
      have : IsIso ((sheafToPresheaf (ProEt.topology Y) _).map f) := by
        change IsIso f.hom
        exact NatIso.isIso_of_isIso_app _
      exact isIso_of_reflects_iso f (sheafToPresheaf (ProEt.topology Y) _)
    exact asIso f
  · intro M N f
    ext U x
    rfl

private def constant_fixed_iso (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) ≅
      adicLisseConstantModules Y A ⋙
        ProFiniteModels.restriction (ProEt.topology Y) A (adicLisseRing Y A)
          (adicLisseConstantUnit Y A) := by
  let J := ProEt.topology Y
  let α := adicLisseConstantUnit Y A
  let R := adicLisseRing Y A
  have hi (M : ModuleCat.{u + 1} A) :
      IsIso (ProFiniteModels.constantComparison J A R α M) :=
    ProFiniteModels.constantComparison_isIso J A R α M
  refine NatIso.ofComponents (fun M ↦ asIso (ProFiniteModels.constantComparison J A R α M)) ?_
  intro M N f
  let a := sheafificationAdjunction J (ModuleCat.{u + 1} A)
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
      ((presheafToSheaf J (ModuleCat.{u + 1} A)).map ((Functor.const Y.ProEtᵒᵖ).map f) ≫
        (ProFiniteModels.constantComparison J A R α N)) =
    a.homEquiv _ _ ((ProFiniteModels.constantComparison J A R α M) ≫ _)
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
  dsimp only [a]
  simp only [ProFiniteModels.constantComparison, Equiv.apply_symm_apply]
  ext U x
  have h := (PresheafOfModules.sheafificationAdjunction α).unit.naturality
    ((siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const Y.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).map f)
  exact congrArg (fun t ↦ t.app U x) h

private def fixed_over_iso (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (α : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj) (V : Y.ProEt) :
    SheafOfModules.overFunctor.{u + 1} R V ⋙
        ProFiniteModels.restriction ((ProEt.topology Y).over V) A (R.over V)
          (Functor.whiskerLeft (Over.forget V).op α) ≅
      ProFiniteModels.restriction (ProEt.topology Y) A R α ⋙
        (ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by ext U x; rfl)

private def restrict_over_iso (Y : Scheme.{u})
    {R S : Sheaf (ProEt.topology Y) RingCat.{u + 1}} (a : R ⟶ S) (V : Y.ProEt) :
    SheafOfModules.overFunctor.{u + 1} S V ⋙
        SheafOfModules.restrictScalars (((ProEt.topology Y).overPullback RingCat.{u + 1} V).map a) ≅
      SheafOfModules.restrictScalars a ⋙ SheafOfModules.overFunctor.{u + 1} R V :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by ext U x; rfl)

set_option maxHeartbeats 800000 in
-- Elaborating the whole tower comparison unfolds several nested restriction functors.
/-- A finite local-system tower trivializes after restricting to one pro-etale cover,
with the entire diagram linear over the completed coefficient ring.
Source: blueprint latest, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-system-completed-trivialization).

Proof: fixed_scalar_cover reuses the adopted simultaneous universal-cover theorem.
The canonical isomorphism from Omega to its algebraic closure transports the point
and its fibre functor. The cover is weakly etale, surjective and quasi-compact;
singleton_cover_of_surjective gives its covering sieve. The natural comparison
between inverse image and localization restriction, followed by precomposition
with the slice-to-localization functor, gives fixed_scalar_slice_iso.

For Q = A/I^(n+1), the tensor/restriction adjunction sends the normalized reduction
map to the sheafification of the constant Q-section map. That map is locally
bijective, so its sheafification is invertible. Since the normalized reduction
map is invertible, the extension unit on constant Q is invertible. Constant
realization, extension and restriction preserve colimits. The rank-one generator
theorem therefore makes this unit invertible on every Q-module. An A-module
annihilated by I^(n+1) has its canonical Q-action, so the same conclusion applies.
Apply this to each stalk. The units are natural even when the annihilating
exponents differ, because they are components of one adjunction unit.

Scalar endomorphisms show that the given tower and its constant tensor model
are killed by the prescribed uniformizer powers. The completed quotient kernel
is generated by constant elements of I^(n+1), so it annihilates both towers.
The constant-to-quotient coefficient map is locally surjective. Thus an A-linear
map between the restricted towers is completed-linear: locally lift a quotient
scalar to constant scalars, subtract the lift, use kernel annihilation, and
then use sheaf separatedness. Lift both directions of the fixed-scalar diagram
isomorphism this way. Their inverse identities and diagram naturality hold on
the unchanged underlying sections. This constructs the asserted isomorphism
on the slice with exactly the specified completed scalar action. No condition
on transition surjectivity or finite generation of an inverse limit is used. -/
theorem finite_system_completed_trivialization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [IsNoetherian Y] [ConnectedSpace Y]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} ((ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))
    (_hSet : ∀ n : ℕ, Scheme.IsSetFLC (H.obj (op n)))
    (_hkill : ∀ (n : ℕ) (V : Y.Etaleᵒᵖ) (x : (H.obj (op n)).obj.obj V),
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))) ^ (n + 1) • x = 0)
    (M : ℕᵒᵖ ⥤ Scheme.proEtaleRingModules Y ((Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))))
    (_eM : M ⋙ (SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u +
    1})).app (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y) (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))) ≅
      H ⋙ comparisonUpperStar (ModuleCat.{u + 1} ((ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))) Y) :
    (∃ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt),
      Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology Y (⊤_ Y.ProEt) ∧
      Nonempty (M ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1}
    ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V) ≅
        (H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))) ⋙ (Scheme.adicLisseConstantModules Y (ULift.{u +
    1} (Padic.coefficientExtensionIntegers l E)) ⋙ Scheme.completedConstantExtension Y
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1,
    u + 1} ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V))) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let π : A := ULift.up (Padic.coefficientExtensionUniformizer l E)
  let I := Ideal.span ({π} : Set A)
  let R := adicLisseRing Y A
  let B := (adicLisseForget Y).obj (adicLisseCompletedRing Y I)
  let c := CompletedConstantReduction.base Y I
  let a := (adicLisseForget Y).map c
  let Res := SheafOfModules.restrictScalars.{u + 1} a
  let RF := ProFiniteModels.restriction (ProEt.topology Y) A R
    (adicLisseConstantUnit Y A)
  let C := adicLisseConstantModules Y A
  let E' := completedConstantExtension Y c
  let N := H ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)
  let F := H ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let K := C ⋙ E'
  have hDvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    hDvr.2.2.2.2.2.2.2.2.1
  have hNoeth : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.symm
  have hH (n : ℕ) : π ^ (n + 1) • 𝟙 (H.obj (op n)) = 0 := by
    ext U x
    exact _hkill n U x
  have hN (n : ℕ) : π ^ (n + 1) • 𝟙 (N.obj (op n)) = 0 := by
    have : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isLeftAdjoint _
    have h := congrArg ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)).map (hH n)
    rw [GrothendieckTopology.Point.sheafFiber_map_smul] at h
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h
    exact h
  have hNt (n : ℕ) :
      Module.IsTorsionBySet A (N.obj (op n)) (↑(I ^ (n + 1)) : Set A) := by
    intro x b
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp
      (show (b : A) ∈ Ideal.span ({π ^ (n + 1)} : Set A) from
        (Ideal.span_singleton_pow π (n + 1)) ▸ b.property)
    rw [← hr, mul_smul]
    have hx : π ^ (n + 1) • x = 0 := congrArg (fun f ↦ f x) (hN n)
    rw [hx, smul_zero]
  have hF (n : ℕ) : π ^ (n + 1) • 𝟙 (F.obj (op n)) = 0 := by
    have h := congrArg (comparisonUpperStar (ModuleCat.{u + 1} A) Y).map (hH n)
    rw [Functor.map_smul] at h
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h
    exact h
  let eM : M ⋙ Res ⋙ RF ≅ F :=
    (Functor.isoWhiskerLeft (M ⋙ Res) (constant_restriction_iso Y A)).symm ≪≫ _eM
  let adj := (ordinaryAdjunction_exists Y c).choose
  have hUnit (j : ℕᵒᵖ) : IsIso (adj.unit.app (C.obj (N.obj j))) :=
    torsion_module_unit_isIso Y I j.unop (N.obj j) (hNt j.unop)
  have : ∀ j, IsIso ((Functor.whiskerLeft (N ⋙ C) adj.unit).app j) := hUnit
  have : IsIso (Functor.whiskerLeft (N ⋙ C) adj.unit) :=
    NatIso.isIso_of_isIso_app _
  let eN : N ⋙ constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) ≅
      (N ⋙ K) ⋙ Res ⋙ RF :=
    Functor.isoWhiskerLeft N (constant_fixed_iso Y A) ≪≫
      Functor.isoWhiskerRight (asIso (Functor.whiskerLeft (N ⋙ C) adj.unit)) RF
  obtain ⟨V, f, hf, ⟨e⟩⟩ := fixed_scalar_cover_object Y Ω y H _hSet
  let eF := fixed_scalar_slice_iso Y V F N e
  let αV := Functor.whiskerLeft (Over.forget V).op (adicLisseConstantUnit Y A)
  let RV := ProFiniteModels.restriction ((ProEt.topology Y).over V) A (R.over V) αV
  let OV := SheafOfModules.overFunctor.{u + 1} B V
  let aV := ((ProEt.topology Y).overPullback RingCat.{u + 1} V).map a
  let ResV := SheafOfModules.restrictScalars.{u + 1} aV
  let G := N ⋙ K
  have : Presheaf.IsLocallySurjective ((ProEt.topology Y).over V) αV :=
    Presheaf.isLocallySurjective_whisker ((ProEt.topology Y).over V)
      (ProEt.topology Y) (Over.forget V) (adicLisseConstantUnit Y A)
  let comm : OV ⋙ ResV ⋙ RV ≅
      Res ⋙ RF ⋙ (ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V :=
    Functor.isoWhiskerRight (restrict_over_iso Y a V) RV ≪≫
      Functor.isoWhiskerLeft Res (fixed_over_iso Y A R (adicLisseConstantUnit Y A) V)
  let eFixed : (M ⋙ OV ⋙ ResV) ⋙ RV ≅ (G ⋙ OV ⋙ ResV) ⋙ RV :=
    Functor.isoWhiskerLeft M comm ≪≫
      Functor.isoWhiskerRight eM
        ((ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V) ≪≫ eF ≪≫
      Functor.isoWhiskerRight eN
        ((ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V) ≪≫
      (Functor.isoWhiskerLeft G comm).symm
  let eR : M ⋙ OV ⋙ ResV ≅ G ⋙ OV ⋙ ResV :=
    ((ProFiniteModels.restrictionFF ((ProEt.topology Y).over V) A (R.over V) αV).whiskeringRight
      ℕᵒᵖ).preimageIso eFixed
  have hMzero (n : ℕ) : π ^ (n + 1) • 𝟙 ((M ⋙ Res ⋙ RF).obj (op n)) = 0 :=
    scalar_zero_of_iso (eM.app (op n)) _ (hF n)
  have hGzero (n : ℕ) : π ^ (n + 1) • 𝟙 ((G ⋙ Res ⋙ RF).obj (op n)) = 0 := by
    apply scalar_zero_of_iso ((eN.app (op n)).symm)
    have h := congrArg (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).map (hN n)
    rw [Functor.map_smul] at h
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h
    exact h
  have hMK (n : ℕ) (U : Y.ProEtᵒᵖ) (b : B.obj.obj U)
      (hb : (limit.π (adicLisseRingSystem Y I) (op n)).hom.app U b = 0)
      (x : (M.obj (op n)).val.obj U) : b • x = 0 := by
    apply completed_kernel_kills Y π n (M.obj (op n)) _ U b hb x
    intro W z
    exact congrArg (fun f ↦ f.hom.app W
      (show ((M ⋙ Res ⋙ RF).obj (op n)).obj.obj W from z)) (hMzero n)
  have hGK (n : ℕ) (U : Y.ProEtᵒᵖ) (b : B.obj.obj U)
      (hb : (limit.π (adicLisseRingSystem Y I) (op n)).hom.app U b = 0)
      (x : (G.obj (op n)).val.obj U) : b • x = 0 := by
    apply completed_kernel_kills Y π n (G.obj (op n)) _ U b hb x
    intro W z
    exact congrArg (fun f ↦ f.hom.app W
      (show ((G ⋙ Res ⋙ RF).obj (op n)).obj.obj W from z)) (hGzero n)
  let d (j : ℕᵒᵖ) : (M ⋙ OV).obj j ≅ (G ⋙ OV).obj j := by
    let q := ((ProEt.topology Y).overPullback RingCat.{u + 1} V).map
      ((adicLisseForget Y).map (limit.π (adicLisseRingSystem Y I) j))
    have : Presheaf.IsLocallySurjective (ProEt.topology Y)
        (a ≫ (adicLisseForget Y).map (limit.π (adicLisseRingSystem Y I) j)).hom :=
      completed_quotient_locallySurjective Y I j.unop
    have : Presheaf.IsLocallySurjective ((ProEt.topology Y).over V) (aV ≫ q).hom :=
      Presheaf.isLocallySurjective_whisker ((ProEt.topology Y).over V)
        (ProEt.topology Y) (Over.forget V)
        (a ≫ (adicLisseForget Y).map (limit.π (adicLisseRingSystem Y I) j)).hom
    exact quotient_scalar_iso aV q ((M ⋙ OV).obj j) ((G ⋙ OV).obj j) (eR.app j)
      (fun U b hb x ↦ hMK j.unop ((Over.forget V).op.obj U) b hb x)
      (fun U b hb x ↦ hGK j.unop ((Over.forget V).op.obj U) b hb x)
  refine ⟨V, f, hf, ⟨NatIso.ofComponents d ?_⟩⟩
  intro i j t
  ext U x
  exact congrArg (fun f ↦ f.val.app U x) (eR.hom.naturality t)

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
