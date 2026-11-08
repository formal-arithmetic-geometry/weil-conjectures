/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import Submission.WeilConjectures.ConstructibleSheaf.Monoidal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finiteness under exact tensor by a finite coefficient line

Source: prop-weil-twist-preserves, proof steps 4--5.
(blueprint: lem-weil-finite-line-tensor-conditions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem constant_unit_over (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) :
    Nonempty (SheafOfModules.unit
        (((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)).over U) ≅
      proEtaleConstantModuleSheafOver S A U
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) := by
  classical
  let J := (ProEt.topology S).over U
  let R := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing S A)).over U
  let a : (Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶ R.obj :=
    Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let := (proEtaleConstantRingUnit_over_locallyBijective S A U).1
  let := (proEtaleConstantRingUnit_over_locallyBijective S A U).2
  let P := proEtaleConstantModulePresheaf (Over U) A
    (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))
  let η : P ⟶ (PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val :=
    { app V := ModuleCat.ofHom (X := P.obj V)
        (Y := ((PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val).obj V)
        { toFun := fun x ↦ a.app V x
          map_add' := fun x y ↦ map_add (a.app V).hom x y
          map_smul' := fun x y ↦ map_mul (a.app V).hom x y }
      naturality f := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (a.naturality f) x) }
  let f : (PresheafOfModules.sheafification.{u + 1} a).obj P ⟶ SheafOfModules.unit R :=
    (PresheafOfModules.sheafificationHomEquiv.{u + 1} a).symm η
  have hfac : toSheafify J P.presheaf ≫
      (PresheafOfModules.toPresheaf R.obj).map f.val =
        Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
    have h := (PresheafOfModules.sheafificationHomEquiv.{u + 1} a (P := P)
      (F := SheafOfModules.unit R)).apply_symm_apply η
    exact (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def a f).symm.trans
      (congrArg (fun g ↦ (PresheafOfModules.toPresheaf _).map g) h)
  have hi : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J a x y h⟩
  have hs : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x ↦ Presheaf.imageSieve_mem J a x⟩
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J _ hfac, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact ⟨(asIso f).symm⟩

private theorem line_constant_models (S : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ ProEt.precoverage S (ProEt.mk (𝟙 S)) ∧
        ∀ i, Nonempty (L.over (U i) ≅ proEtaleConstantModuleSheafOver S A (U i)
          (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) := by
  classical
  obtain ⟨I, U, hc, he⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp inferInstance
  obtain ⟨Q, hQ, hle⟩ := ProEt.mem_topology_iff.mp (hc (ProEt.mk (𝟙 S)))
  let V : Q.uncurry → S.ProEt := fun i ↦ i.1.1
  let f : ∀ i : Q.uncurry, V i ⟶ ProEt.mk (𝟙 S) := fun i ↦ i.1.2
  have hQeq : Presieve.ofArrows V f = Q := by
    funext W g
    apply propext
    constructor
    · rintro ⟨i⟩
      exact i.2
    · intro hg
      exact @Presieve.ofArrows.mk _ _ _ _ V f ⟨⟨W, g⟩, hg⟩
  refine ⟨Q.uncurry, V, f, hQeq.symm ▸ hQ, ?_⟩
  intro i
  obtain ⟨j, ⟨g⟩⟩ := hle _ _ i.2
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  let e := (he j).some ≪≫ SheafOfModules.freeUniqueIso _
  let e' : L.over (V i) ≅ SheafOfModules.unit (R.over (V i)) :=
    ((SheafOfModules.overFunctorMap R g).app L).symm ≪≫
      (SheafOfModules.overMap R g).mapIso e ≪≫ SheafOfModules.overMapUnitIso (R := R) g
  exact ⟨e' ≪≫ (constant_unit_over S A (V i)).some⟩

private theorem line_finite_models (S : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1] :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((proEtaleModuleRestriction S A).obj L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := line_constant_models S A L
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a (ModuleCat.of B B)
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B) :=
    E.mapIso (he i).some ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a (ModuleCat.of B B))).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app (ModuleCat.of B B)
  exact ⟨ModuleCat.of B B, inferInstance, ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

end WeilConjectures
