/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitIsIso
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Equality detection for inverse orientation maps

Source: orientation-charts Step 4, expanded in the parent orientation node.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

private theorem base_normal_form (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (affineLinearBaseCoefficient A N hA S d ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)))⟦2 * (d : ℤ)⟧) := by
  let E := fun d : ℕ ↦ Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)
  have hflat (d : ℕ) : ObjectProperty.flat (E d) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line S N hN
      (fun x ↦ by
        simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom)
      A hA d).2.2.1
  let t := Scheme.finiteEtaleTwistPullbackData A N hN hA
  induction d with
  | zero =>
    exact ⟨(Iso.refl _) ≪≫ (shiftFunctorZero _ ℤ).symm.app _⟩
  | succ d ih =>
    obtain ⟨e⟩ := ih
    let prod : E d ⊗ E 1 ≅ E (d + 1) :=
      t.p S hS d 1 ≪≫ eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N S hA)
        (by omega))
    refine ⟨((derivedTensorRight (ModuleCat.{u + 1} A) S
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).mapIso e) ≪≫ ?_⟩
    exact derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ (2 * (d : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
        (singleProductGeneral (ModuleCat.{u + 1} A) S (E d) (E 1) (E (d + 1))
          (hflat d) prod) ≪≫
      eqToIso (congrArg (fun a : ℤ ↦
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (E (d + 1)))⟦a⟧) (by omega))

private theorem exists_affine_frame (S : Scheme.{u}) (d : ℕ) (M : S.Modules)
    [M.IsFiniteLocallyFreeOfRank d] (x : S) :
    ∃ V : S.affineOpens, x ∈ V.1 ∧
      Nonempty (VectorBundleZeroSection.Trivialization S d M V.1) := by
  classical
  obtain ⟨I, W, hW, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hW.ge (Set.mem_univ x))
  obtain ⟨V, hV, hx, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hi
  have : (Scheme.Modules.restrictFunctor (S.homOfLE hVW)).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction (S.homOfLE hVW)).isLeftAdjoint
  refine ⟨⟨V, hV⟩, hx, ⟨?_⟩⟩
  exact Scheme.Modules.restrictCompIso M (W i).ι (S.homOfLE hVW) (Scheme.Opens.ι V)
      (Scheme.homOfLE_ι S hVW) ≪≫
    (Scheme.Modules.restrictFunctor (S.homOfLE hVW)).mapIso (e i).some ≪≫
    (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor (S.homOfLE hVW))
      (ULift.{u} (Fin d)) (Scheme.Modules.restrictUnitIso (S.homOfLE hVW)).symm).symm

private theorem map_eq_of_cover (A : Type (u + 1)) [CommRing A]
    {S : Scheme.{u}} {I : Type u} (U : I → S.Opens)
    (hU : ∀ x : S, ∃ i : I, x ∈ U i)
    {K L : DerivedCategoryModule A S} (n : ℤ)
    [K.IsLE n] [L.IsGE n] (f g : K ⟶ L)
    (h : ∀ i, (ordinaryFinitePullback A (U i).ι).map f =
      (ordinaryFinitePullback A (U i).ι).map g) : f = g := by
  apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).injective
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} A) (U i).ι) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N z hz
    apply isIso_of_isIso_upperStar_map_of_jointlySurjective
      (ModuleCat.{u + 1} A) (fun i ↦ (U i).ι) ?_ z hz
    intro x
    obtain ⟨i, hi⟩ := hU x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  apply hf.map_injective
  intro i
  have hh : (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map f =
      (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map g := by
    let c := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (U i).ι
    exact (NatIso.naturality_1 c f).symm.trans
      ((congrArg (fun z ↦ c.inv.app K ≫ z ≫ c.hom.app L) (h i)).trans
        (NatIso.naturality_1 c g))
  let e := (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategoryHomologyFunctorIso n
  exact (NatIso.naturality_2 e f).symm.trans
    ((congrArg (fun z ↦ e.hom.app K ≫ z ≫ e.inv.app L)
      ((_root_.DerivedCategory.homologyFunctor _ n).congr_map hh)).trans
        (NatIso.naturality_2 e g))

/-- Maps from the shifted Tate coefficient to the section dualizing object are detected
on affine linear frames, even after the specified chart comparison.
Source: orientation-charts Step 4; parent proof Steps 2--3 and 6.
(blueprint: lem-trf-bundle-section-orientation-map-ext).

Proof: tensor products of flat finite Tate lines identify the source with the single
sheaf A(d) shifted by 2d. The coefficient-unit integration mate is invertible, so its
zero-section pullback identifies the target with that same shifted single sheaf.
Refine local module frames to an affine cover. The exceptional comparison for each
frame is invertible by open base change; cancel it from the assumed equations.
Cohomology in degree -2d is injective on Hom between these concentrated objects.
Exact restriction commutes with cohomology, and the restrictions to the affine cover
are jointly faithful on sheaves. Therefore the cohomology maps, and then the original
maps, agree. Empty bases are covered by the same jointly-surjective-family statement;
zero coefficients and rank zero require no modification. -/
theorem bundleSectionOrientation_map_ext (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (f g : affineLinearBaseCoefficient A N hA S d ⟶ bundleSectionObject A S d M)
    (h : ∀ (V : S.Opens) (_hV : IsAffine V.toScheme)
      (e : VectorBundleZeroSection.Trivialization S d M V),
      (ordinaryFinitePullback A V.ι).map f ≫ bundleSectionChartComparison A S d M V e =
        (ordinaryFinitePullback A V.ι).map g ≫
          bundleSectionChartComparison A S d M V e) : f = g := by
  classical
  obtain ⟨p, hp, hm⟩ := bundleSectionPurityUnit_exists_isIso N hN A hA S hS d M
  let q := (bundleSectionCoefficientIso A N hA S d M).inv ≫
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
      (bundleSectionPurityUnitMap N hN A hA S hS d M p)
  have : IsIso q := IsIso.comp_isIso' (Iso.isIso_inv _) (Functor.map_isIso _ _)
  obtain ⟨e⟩ := base_normal_form N hN A hA S hS d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ))
  have hle : _root_.DerivedCategory.TStructure.t.IsLE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have hge : _root_.DerivedCategory.TStructure.t.IsGE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have : (affineLinearBaseCoefficient A N hA S d).IsLE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm _
  have : (bundleSectionObject A S d M).IsGE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso (e.symm ≪≫ asIso q) _
  choose V hx eV using exists_affine_frame S d M
  apply map_eq_of_cover A (fun x : S ↦ (V x).1) (fun x ↦ ⟨x, hx x⟩)
    (-(2 * (d : ℤ))) f g
  intro x
  let e := (eV x).some
  have hc : IsIso (bundleSectionChartComparison A S d M (V x).1 e) := by
    have hb := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A
      (vectorIntegrationChart_isPullback S d M (V x).1 e)
    dsimp only [bundleSectionChartComparison, bundleSectionComparison]
    infer_instance
  exact (cancel_mono (bundleSectionChartComparison A S d M (V x).1 e)).1
    (h (V x).1 (V x).2 e)

end AlgebraicGeometry.Etale
