/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedCechComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual

/-! # Completed pullback on the published completed-coefficient categories

Source: Stacks proetale.tex, Tag 099N (2),(5), blueprint order 1261.
(blueprint: lem-weil-pbc-ringed-topoi-module-adjunction)
The coefficient structure is fixed on all quotient projections. Ordinary pullback
is its total derived sheafified tensor inverse image. Completion is characterized
by its reflection universal property on the actual intrinsic complete subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.

-- Transport the unit along the K-injective equivalence, then detect it on resolutions.

namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- Universality of the named ordinary left derived pair.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: unfold the named functor and counit. They are the universal pair selected
from completedOrdinaryPullback_exists, whose first property is the assertion. -/
@[instance] theorem pbcActualPullUniversal :
    (pbcActualDerivedPull g d).IsLeftDerivedFunctor (pbcActualPullCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold pbcActualDerivedPull completedOrdinaryPullback pbcActualPullCounit
    completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.1

/-- Universality of the named ordinary right derived pair.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: unfold its totalRightDerived and unit; the universal Kan-extension
construction gives IsRightDerivedFunctor. -/
@[instance] theorem pbcActualDirectUniversal :
    (pbcActualDerivedPush g d).IsRightDerivedFunctor
      (pbcActualPushUnit g d)
        (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  dsimp [pbcActualDerivedPush, pbcActualPushUnit]
  infer_instance

-- `moduleBinaryBiproducts` has a free universe and leaves a stuck universe constraint here.
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts in
/-- The resolving left derived pair remains universal after the indicated direct image.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the K-flat resolving construction is pointwise and hence absolute.
Postcomposition by ordinary derived direct image preserves its universal derived
comparison; equivalently compute at a resolving complex, where the counit is
invertible. This gives the stated universal left derived pair. -/
@[instance] theorem pbcActualDerivedLeftComposite :
    (pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d))
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  let C := pbcModules Y (pbcAdicCompletion Y d)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let B := ((pbcActualModulePull g d).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh) ⋙ pbcActualDerivedPush g d
  let L := pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d
  let α : DerivedCategory.Qh ⋙ L ⟶ B :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d)
  let P : Set (HomotopyCategory C (.up ℤ)) :=
    { Z | IsIso ((pbcActualPullCounit g d).app Z) }
  have hres (Z : HomotopyCategory C (.up ℤ)) :
      ∃ (Z' : HomotopyCategory C (.up ℤ)) (s : Z' ⟶ Z), Z' ∈ P ∧ W s := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    obtain ⟨K', s, hK', _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) K
    refine ⟨_, (HomotopyCategory.quotient C (.up ℤ)).map s, ?_,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    change IsIso ((pbcActualPullCounit g d).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K'))
    unfold pbcActualPullCounit completedOrdinaryPullbackCounit completedOrdinaryPullback
    exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.2 K' hK'
  have hcompute (Z : HomotopyCategory C (.up ℤ)) (hZ : Z ∈ P) : IsIso (α.app Z) := by
    have : IsIso ((pbcActualPullCounit g d).app Z) := hZ
    change IsIso (𝟙 _ ≫ (pbcActualDerivedPush g d).map
      ((pbcActualPullCounit g d).app Z))
    rw [Category.id_comp]
    infer_instance
  have hinv (Z Z' : HomotopyCategory C (.up ℤ)) (s : Z ⟶ Z')
      (hZ : Z ∈ P) (hZ' : Z' ∈ P) (hs : W s) : IsIso (B.map s) := by
    have := hcompute Z hZ
    have := hcompute Z' hZ'
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh W s hs
    have heq : B.map s = inv (α.app Z) ≫ L.map (DerivedCategory.Qh.map s) ≫ α.app Z' := by
      apply (cancel_epi (α.app Z)).1
      simpa only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc] using
        (α.naturality s).symm
    rw [heq]
    infer_instance
  obtain ⟨_, L', ε, hL', _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory (pbcModules Y
      (pbcAdicCompletion Y d))) B P hres hinv
  have := hL'
  let δ := L'.leftDerivedLift ε W L α
  have hδ (Z : HomotopyCategory C (.up ℤ)) (hZ : Z ∈ P) :
      IsIso (δ.app (DerivedCategory.Qh.obj Z)) := by
    have := hε Z hZ
    have := hcompute Z hZ
    have heq : δ.app (DerivedCategory.Qh.obj Z) = α.app Z ≫ inv (ε.app Z) := by
      apply (cancel_mono (ε.app Z)).1
      simp [δ]
    rw [heq]
    infer_instance
  have : IsIso δ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have := Localization.essSurj (DerivedCategory.Qh (C := C)) W
    let Z := (DerivedCategory.Qh (C := C)).objPreimage K
    obtain ⟨Z', s, hZ', hs⟩ := hres Z
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh W s hs
    let e : DerivedCategory.Qh.obj Z' ≅ K := asIso (DerivedCategory.Qh.map s) ≪≫
      (DerivedCategory.Qh (C := C)).objObjPreimageIso K
    exact (NatTrans.isIso_app_iff_of_iso δ e).1 (hδ Z' hZ')
  exact (L'.isLeftDerivedFunctor_iff_isIso_leftDerivedLift ε W L α).2 this

/-- The resolving right derived pair remains universal after the indicated pullback.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the K-injective resolving construction is pointwise and hence absolute.
Postcomposition by ordinary derived pullback preserves its universal derived
comparison; equivalently compute at a K-injective complex, where the unit is
invertible. This gives the stated universal right derived pair. -/
@[instance] theorem pbcActualDerivedRightComposite :
    (pbcActualDerivedPush g d ⋙ pbcActualDerivedPull g d).IsRightDerivedFunctor
      (whiskerRight (pbcActualPushUnit g d) (pbcActualDerivedPull g d) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  apply (HomotopyCategory.KInjectives.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
  intro I
  obtain ⟨I, hI, rfl⟩ := I.mk_surjective
  have : I.IsKInjective := hI
  have : IsIso ((pbcActualModulePush g d).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj I)) := inferInstance
  change IsIso ((pbcActualDerivedPull g d).map
    ((pbcActualModulePush g d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)) ≫ 𝟙 _)
  infer_instance

-- The two coefficient presentations have equivalent module and derived categories.
-- These transport arguments are the existing ones used by WeilTensorProduct.
section CompletionPresentation
variable (X)
variable (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip wfRestrictId

attribute [local irreducible] intrinsicCompletionComplex

-- The Cech functor has the same essential image as the Koszul reflection.
-- Its shift isomorphism therefore supplies shift closure without expanding the fiber.

end CompletionPresentation

variable (T : Scheme.{u})

/-- The intrinsic complete subcategory is reflective, with the Koszul completion unit.
Source: 099N (2),(5), 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
Proof: the derived inverse limit of the strict negative-Koszul tower is completion.
Its degree-zero augmentation is a reflection unit, by ringed-koszul-completion-reflector.
Transport the comparison through pbcCompletedComparison. This preserves the unit,
so the predicate is exactly PbcIsIntrinsicallyComplete, even over the empty scheme.
The reflection property determines the output and unit up to unique isomorphism. -/
@[instance] theorem pbcActualCompleteInclusion_isRightAdjoint :
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).IsRightAdjoint := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let P : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let W := wfCompletion T d r a ha
  let L : PbcCompletedDerived T d ⥤ P.FullSubcategory :=
    P.lift (W ⋙ ObjectProperty.ι _) (fun M ↦
      (wfComplete_iff_presentation T d r a ha _).mp (W.obj M).property)
  let e (M : PbcCompletedDerived T d) (N : P.FullSubcategory) :
      (L.obj M ⟶ N) ≃ (M ⟶ N.obj) :=
    (ObjectProperty.fullyFaithfulι P).homEquiv.trans
      (Equiv.ofBijective _ ((wfCompletionReflector T d r a ha).2 M N.obj
        ((wfComplete_iff_presentation T d r a ha N.obj).mpr N.property)))
  let adj : L ⊣ P.ι := Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro M M' N f h
        apply (e M N).injective
        symm
        change wfCompletionUnit T d r a ha M ≫
          (L.map f ≫ (e M' N).symm h).hom = _
        dsimp only [ObjectProperty.FullSubcategory.comp_hom]
        rw [← Category.assoc]
        have hn : wfCompletionUnit T d r a ha M ≫ (L.map f).hom =
            f ≫ wfCompletionUnit T d r a ha M' := by
          exact (Equiv.ofBijective _ ((wfCompletionReflector T d r a ha).2 M
            (wfCompletionObj T d r a ha M')
            ((wfCompletionReflector T d r a ha).1 M'))).apply_symm_apply _
        rw [hn, Category.assoc]
        change f ≫ (e M' N) ((e M' N).symm h) = (e M N) ((e M N).symm (f ≫ h))
        simp
      homEquiv_naturality_right := by
        intro M N N' h f
        change wfCompletionUnit T d r a ha M ≫ (h ≫ f).hom =
          (wfCompletionUnit T d r a ha M ≫ h.hom) ≫ f.hom
        exact (Category.assoc _ _ _).symm }
  exact ⟨L, ⟨adj⟩⟩

-- Use the published perfect-projection tower mate and its completion-unit equation.

end AlgebraicGeometry.Scheme
