/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-! # Derived tensor comparison for the trivialized Kummer sheaf

The root calculation supplies bounded flat cohomology. Stacks 0F12 gives the
constant-complex projection isomorphism; flat degree-zero normalization identifies
its sheaf side, and the flat-cohomology edge map gives the ordinary coefficient
comparison. Naturality is retained throughout.
(blueprint: lem-pur-kummer-derived-coefficient-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

private def residueLinear (m : ℕ) {M P : Type (u + 1)}
    [AddCommGroup M] [AddCommGroup P]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module (ULift.{u + 1} (ZMod m)) P]
    (f : M →+ P) : M →ₗ[ULift.{u + 1} (ZMod m)] P :=
  { f with
    map_smul' := by
      intro r x
      have hr : r = ((ZMod.cast r.down : ℤ) : ULift.{u + 1} (ZMod m)) := by
        apply ULift.ext
        exact (ZMod.intCast_zmod_cast r.down).symm
      change f (r • x) = r • f x
      rw [hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }

private instance residueForgetFull (m : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}).Full where
  map_surjective {_A _B} f := ⟨ModuleCat.ofHom (residueLinear m f.hom), rfl⟩

private def rootModuleSheaf (C : Scheme.{u}) (m : ℕ) :
    Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :=
  ⟨kummerRootModulePresheaf C m, by
    apply (Presheaf.isSheaf_of_isSheaf_comp C.smallEtaleTopology _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}))
    exact (C.rootsOfUnitySheaf m).property⟩

private def rootModuleConstantIso (C : Scheme.{u}) (m : ℕ)
    (θ : C.rootsOfUnitySheaf m ≅ C.constantZMod m) :
    rootModuleSheaf C m ≅
      (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) := by
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat
  let V := sheafCompose C.smallEtaleTopology U
  exact V.preimageIso (θ ≪≫ (Etale.constantSheafSheafComposeForget₂Iso (Y := C)
    (ULift.{u + 1} (ZMod m))).symm.app
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))))

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private def twistConstantFunctorIso (C : Scheme.{u}) (m : ℕ)
    (θ : C.rootsOfUnitySheaf m ≅ C.constantZMod m) :
    kummerModuleTwist C m ≅
      constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) := by
  let F := presheafToSheaf C.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
  let Q := rootModuleSheaf C m
  let e : F.obj Q.obj ≅ 𝟙_ _ :=
    (sheafificationIso Q).symm ≪≫ rootModuleConstantIso C m θ ≪≫
      (Functor.Monoidal.εIso F).symm
  exact Functor.isoWhiskerLeft (Functor.const C.Etaleᵒᵖ)
      (Functor.Monoidal.commTensorLeft F Q.obj).symm ≪≫
    Functor.isoWhiskerLeft (Functor.const C.Etaleᵒᵖ ⋙ F)
      ((curriedTensor _).mapIso e ≪≫ leftUnitorNatIso _)

private def unitInsertionIso (C : Scheme.{u}) (m : ℕ) :
    rootModuleSheaf C m ≅
      (kummerModuleTwist C m).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) :=
  sheafificationIso (rootModuleSheaf C m) ≪≫
    (presheafToSheaf C.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))).mapIso
        (ρ_ (kummerRootModulePresheaf C m)).symm

private lemma unitInsertionIso_hom (C : Scheme.{u}) (m : ℕ) :
    (sheafCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1})).map
        (unitInsertionIso C m).hom =
      kummerCoefficientInsertion C m
        (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) 1 := by
  apply Sheaf.hom_ext
  ext U x
  have h := congrArg (fun g ↦ g.app U)
    (toSheafify_naturality C.smallEtaleTopology
      (ρ_ (kummerRootModulePresheaf C m)).inv)
  exact (congrArg (fun g ↦ g x) h).symm


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.KummerDerived

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

private abbrev constants := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
private abbrev global := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} R) X
private abbrev K := (global R X).obj (𝟙_ _)
private abbrev H (q : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) q

/-- Flat degree-zero normalization for the native constant-module tensor unit: the
rank-one case of flat-single normalization (lem-pur-flat-single-derived-normalization,
Stacks 06YU, 07A4). Tensoring with the unit is the derived left unitor; the exact
constant-sheaf functor commutes with the single-complex embedding. -/
private def normalize :
    DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0 ⋙
        (constants R X).leftDerivedFunctor ⋙ tensorLeft (𝟙_ _) ≅
      constants R X ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0)
      (Functor.isoWhiskerLeft (constants R X).leftDerivedFunctor (leftUnitorNatIso _)) ≪≫
    (constants R X).singleFunctorCompLeftDerivedFunctorIso

private def comparison
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hR : ∃ n : ℕ, 0 < n ∧ (n : R) = 0)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((H R i).obj (K R X)))
    (hflat : ∀ i : ℤ, Module.Flat R ((H R i).obj (K R X))) (q : ℤ) :
    tensorLeft ((H R q).obj (K R X)) ≅
      constants R X ⋙ DerivedCategory.singleFunctor _ 0 ⋙ global R X ⋙ H R q :=
  beta R X hbounded hflat q ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0)
        (projection R X hcd hR)) (H R q) ≪≫
    Functor.isoWhiskerRight (normalize R X) (global R X ⋙ H R q)

end AlgebraicGeometry.KummerDerived

namespace AlgebraicGeometry.KummerDerived

private def moduleForgetIso (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) (q : ℕ) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} R) X q) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ≅
      sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ⋙
        Sheaf.functorH X.smallEtaleTopology q :=
  (Scheme.nonempty_etaleModuleCohomology_forgetIso X R q).some ≪≫
    Functor.isoWhiskerLeft _ (Scheme.nonempty_sheafH_extDerivedIso X q).some.symm

private def unitRootIso (X : Scheme.{u}) (m : ℕ)
    (θ : X.rootsOfUnitySheaf m ≅ X.constantZMod m) :
    𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))) ≅
      Scheme.rootModuleSheaf X m :=
  Functor.Monoidal.εIso (constants (ULift.{u + 1} (ZMod m)) X) ≪≫
    (Scheme.rootModuleConstantIso X m θ).symm

private def rootHomologyIso (X : Scheme.{u}) (m : ℕ)
    (θ : X.rootsOfUnitySheaf m ≅ X.constantZMod m) (q : ℕ) :
    (H (ULift.{u + 1} (ZMod m)) q).obj (K (ULift.{u + 1} (ZMod m)) X) ≅
      ModuleCat.of (ULift.{u + 1} (ZMod m)) (Sheaf.H (X.rootsOfUnitySheaf m) q) := by
  let R := ULift.{u + 1} (ZMod m)
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let V := sheafCompose X.smallEtaleTopology U
  let e : U.obj ((H R q).obj (K R X)) ≅
      (Sheaf.functorH X.smallEtaleTopology q).obj (X.rootsOfUnitySheaf m) :=
    U.mapIso ((Etale.cohomology (ModuleCat.{u + 1} R) X q).mapIso
        (DerivedCategory.singleFunctorObjUnitIso _).symm) ≪≫
      (moduleForgetIso R X q).app (𝟙_ _) ≪≫
      (Sheaf.functorH X.smallEtaleTopology q).mapIso (V.mapIso (unitRootIso X m θ))
  exact (LinearEquiv.ofBijective (Scheme.residueLinear m
    (M := (H R q).obj (K R X))
    (P := Sheaf.H (X.rootsOfUnitySheaf m) q) e.hom.hom)
    (ConcreteCategory.bijective_of_isIso e.hom)).toModuleIso

private theorem rootHomology_bounded (X : Scheme.{u}) (m : ℕ)
    (θ : X.rootsOfUnitySheaf m ≅ X.constantZMod m)
    (d : ℕ) (hv : ∀ q : ℕ, d < q → Subsingleton (Sheaf.H (X.rootsOfUnitySheaf m) q)) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((H (ULift.{u + 1} (ZMod m)) i).obj (K (ULift.{u + 1} (ZMod m)) X)) := by
  let R := ULift.{u + 1} (ZMod m)
  refine ⟨0, d, ?_⟩
  intro i hi
  by_cases h : i < 0
  · have hge : ((global R X).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} R)) 0).obj (𝟙_ _))).IsGE 0 :=
      Functor.isGE_rightDerivedFunctor_obj_singleFunctor
        (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R)) (𝟙_ _)
    exact (DerivedCategory.isZero_of_isGE _ 0 i h).of_iso
      ((H R i).mapIso ((global R X).mapIso
        (DerivedCategory.singleFunctorObjUnitIso _).symm))
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
    have := hv q (by omega)
    exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).of_iso
      (rootHomologyIso X m θ q)

/-- The derived coefficient comparison for a trivialized root sheaf with bounded flat
cohomology. No flatness of the coefficient module is assumed.
Source: the coefficient step of thm-pur-kummer-affine-line.proof.md, Stacks 0F12 and 0H7Z
(blueprint: lem-pur-kummer-derived-coefficient-comparison).

Proof: use the root trivialization to identify its module sheaf with the tensor unit.
The flat degree-zero normalization is then the derived left unitor together with the
exact constant functor's single-complex comparison. Apply the actual constant projection
map (0F12), and the canonical flat-cohomology edge map (0H7Z). The module-forgetting and
Ext/derived cohomology comparisons identify the result with the published abelian
cohomology functor. Every comparison is natural in the coefficient module. Negative
cohomology vanishes by right-derived left exactness; the supplied root bound handles
positive degrees. Additive maps between residue modules are linear, so the root comparison
transports flatness. Unit insertion is the inverse ordinary right unitor followed by
sheafification, independently of the coefficient computation. -/
theorem kummer_derived_coefficient_comparison (X : Scheme.{u}) (m : ℕ)
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hm : 0 < m) (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (θ : X.rootsOfUnitySheaf m ≅ X.constantZMod m)
    (d : ℕ) (hv : ∀ q : ℕ, d < q → Subsingleton (Sheaf.H (X.rootsOfUnitySheaf m) q))
    (hf : ∀ q : ℕ, Module.Flat (ULift.{u + 1} (ZMod m))
      (Sheaf.H (X.rootsOfUnitySheaf m) q)) :
    (∀ q : ℕ, Nonempty
      (tensorLeft (ModuleCat.of (ULift.{u + 1} (ZMod m))
          (Sheaf.H (X.rootsOfUnitySheaf m) q)) ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} ≅
        Scheme.kummerAbelianTwist X m ⋙ Sheaf.functorH X.smallEtaleTopology q)) ∧
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}).Full ∧
    IsIso (Scheme.kummerCoefficientInsertion X m
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) 1) := by
  let R := ULift.{u + 1} (ZMod m)
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let V := sheafCompose X.smallEtaleTopology U
  have hbound := rootHomology_bounded X m θ d hv
  have hflat (i : ℤ) : Module.Flat R ((H R i).obj (K R X)) := by
    by_cases hi : i < 0
    · have hge : ((global R X).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} R)) 0).obj (𝟙_ _))).IsGE 0 :=
        Functor.isGE_rightDerivedFunctor_obj_singleFunctor
          (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R)) (𝟙_ _)
      have hz : IsZero ((H R i).obj (K R X)) :=
        (DerivedCategory.isZero_of_isGE _ 0 i hi).of_iso
          ((H R i).mapIso ((global R X).mapIso
            (DerivedCategory.singleFunctorObjUnitIso _).symm))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
      have := hf q
      exact Module.Flat.of_linearEquiv (rootHomologyIso X m θ q).toLinearEquiv
  refine ⟨?_, inferInstance, ?_⟩
  · intro q
    let c := comparison R X hcd ⟨m, hm, by simp [R]⟩ hbound hflat q
    exact ⟨Functor.isoWhiskerRight
        ((curriedTensor (ModuleCat.{u + 1} R)).mapIso (rootHomologyIso X m θ q).symm) U ≪≫
      Functor.isoWhiskerRight c U ≪≫
      Functor.isoWhiskerLeft (constants R X) (moduleForgetIso R X q) ≪≫
      Functor.isoWhiskerRight (Scheme.twistConstantFunctorIso X m θ).symm
        (V ⋙ Sheaf.functorH X.smallEtaleTopology q)⟩
  · rw [← Scheme.unitInsertionIso_hom]
    infer_instance

end AlgebraicGeometry.KummerDerived
