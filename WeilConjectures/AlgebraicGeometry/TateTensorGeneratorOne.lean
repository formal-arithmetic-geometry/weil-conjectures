/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorGeneratorCompatibility
import WeilConjectures.AlgebraicGeometry.RootTowerFiniteTensor
import all WeilConjectures.AlgebraicGeometry.FiniteRootSiteComparison
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatumSupplement

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-one)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower
open scoped TensorProduct ChangeOfRings

private def rootUnit (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    purTwistZlOne T ell ⟶ (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} ((adicLisseForget T).obj
      (pbcAdicCompletion T (datum.{u} ell)))).obj (integralLine T ell 1) where
  hom :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        (((@SheafOfModules.CochainScalarConstruction.pureBilin.{u + 1, u + 1, u}
          T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
          (ProEt.topology T) inferInstance
          (pbcAdicCompletion T (datum.{u} ell))
          (SheafOfModules.unit.{u, u + 1, u + 1}
            ((adicLisseForget T).obj (pbcAdicCompletion T (datum.{u} ell))))
          (integralRoot T ell) W)
          (show (integralLine T ell 0).val.obj W from
            (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj W))).toAddMonoidHom)
      naturality := by
        intro U V v
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        have h := @SheafOfModules.CochainScalarConstruction.pure_restrict.{u + 1, u + 1, u}
          T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
          (ProEt.topology T) inferInstance
          (pbcAdicCompletion T (datum.{u} ell))
          (SheafOfModules.unit.{u, u + 1, u + 1}
            ((adicLisseForget T).obj (pbcAdicCompletion T (datum.{u} ell))))
          (integralRoot T ell) U V v
            (show (integralLine T ell 0).val.obj U from
              (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj U)) x
        have hone :
            (SheafOfModules.unit ((adicLisseForget T).obj
              (pbcAdicCompletion T (datum.{u} ell)))).val.map v
                (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj U) =
              (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj V) :=
          PresheafOfModules.unit_map_one _ v
        rw [hone] at h
        dsimp only [SheafOfModules.CochainScalarConstruction.pureBilin,
          SheafOfModules.CochainScalarConstruction.pureMap]
        exact h.symm }

private def rootIntoQuotient (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    purTwistZlOne T ell ⟶ (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} ((adicLisseForget T).obj
      ((pbcAdicRings T (datum.{u} ell)).obj (op n)))).obj (quotientLine T ell n 1) :=
  rootUnit T ell ≫ (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} _).map
    ((pbcScalarAdjunction (pbcAdicProjection T (datum.{u} ell) n)).unit.app
      (integralLine T ell 1))

private theorem rootIntoQuotient_apply (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (W : T.ProEtᵒᵖ) (x : (purTwistZlOne T ell).obj.obj W) :
    (rootIntoQuotient T ell n).hom.app W x =
      pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n) (integralLine T ell 1) W 1
        (integralGenerator T ell W 1 (fun _ ↦ x)) := by
  change ((pbcScalarAdjunction (pbcAdicProjection T (datum.{u} ell) n)).unit.app
    (integralLine T ell 1)).val.app W _ = _
  have h := (pbcScalarAdjunction_exists (pbcAdicProjection T (datum.{u} ell) n)).exists.choose_spec
    (integralLine T ell 1) W ((rootUnit T ell).hom.app W x)
  have hu : (rootUnit T ell).hom.app W x =
      integralGenerator T ell W 1 (fun _ ↦ x) := by
    rfl
  rw [hu] at h
  exact h


private theorem quotient_killed (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (W : T.ProEtᵒᵖ) (x : (quotientLine T ell n 1).val.obj W) :
    ell ^ (n + 1) • x = 0 := by
  have h : ((ell ^ (n + 1) : ℕ) :
      ((pbcAdicRings T (datum.{u} ell)).obj (op n)).obj.obj W) = 0 := by
    have hzero : ((ell ^ (n + 1) : ℕ) : coefficient ell (n + 1)) = 0 :=
      CharP.cast_eq_zero _ _
    exact (map_natCast ((scalars T ell n).app W).hom _).symm.trans
      ((congrArg ((scalars T ell n).app W) hzero).trans (map_zero _))
  rw [← Nat.cast_smul_eq_nsmul
    (((pbcAdicRings T (datum.{u} ell)).obj (op n)).obj.obj W), h, zero_smul]

private theorem root_descends (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ) :
    ∃ f : proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ⟶
        (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} ((adicLisseForget T).obj
          ((pbcAdicRings T (datum.{u} ell)).obj (op n)))).obj (quotientLine T ell n 1),
      rootTowerProjection T ell n ≫ f = rootIntoQuotient T ell n := by
  have hstalk (t : T) : IsUnit (ell : T.presheaf.stalk t) := by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  obtain ⟨hs, hk, _⟩ := rootTower_finite_tensor T ell hstalk n
  have : Epi (rootTowerProjection T ell n) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
      (rootTowerProjection T ell n)).mp hs
  have hz : kernel.ι (rootTowerProjection T ell n) ≫ rootIntoQuotient T ell n = 0 := by
    ext W z
    let x := (kernel.ι (rootTowerProjection T ell n)).hom.app W z
    have hx : (rootTowerProjection T ell n).hom.app W x = 0 :=
      congrArg (fun f ↦ f.hom.app W z) (kernel.condition (rootTowerProjection T ell n))
    obtain ⟨y, hy⟩ := (hk W.unop x).mp hx
    change (rootIntoQuotient T ell n).hom.app W x = 0
    rw [← hy, map_nsmul]
    exact quotient_killed T ell n W _
  exact ⟨Abelian.epiDesc _ _ hz, Abelian.comp_epiDesc _ _ hz⟩

private def fixedCoefficients (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (N : pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1))) := by
  let P := (PresheafOfModules.restrictScalars (scalars T ell n)).obj N.val
  let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (coefficient ell (n + 1)) :=
    { obj := P.obj
      map := P.map
      map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
      map_comp f g := by
        ext x
        exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) F
    (forget₂ (ModuleCat.{u + 1} (coefficient ell (n + 1))) AddCommGrpCat.{u + 1})
    N.isSheaf⟩

attribute [local semireducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

private theorem rootTensorLift (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (d : proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ⟶
      (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} ((adicLisseForget T).obj
        ((pbcAdicRings T (datum.{u} ell)).obj (op n)))).obj (quotientLine T ell n 1)) :
    ∃ f : finiteRootProTensor (coefficient ell (n + 1)) (ell ^ (n + 1))
        (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _) T ⟶
      fixedCoefficients T ell n (quotientLine T ell n 1),
      ∀ W a z, f.hom.app W
        (finiteRootProGenerator (coefficient ell (n + 1)) (ell ^ (n + 1))
          (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _) T W a z) =
        ((scalars T ell n).app W).hom a •
          (show (quotientLine T ell n 1).val.obj W from d.hom.app W z) := by
  let A := coefficient ell (n + 1)
  let m := ell ^ (n + 1)
  let hm := pow_pos (Fact.out : ell.Prime).pos (n + 1)
  let hA : (m : A) = 0 := CharP.cast_eq_zero _ _
  let F := fixedCoefficients T ell n (quotientLine T ell n 1)
  let d' : proEtaleRootsOfUnitySheaf T m ⟶
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F := d
  let f := (proLineHomEquiv T m hm A hA F).symm d'
  have h1 (W : T.ProEtᵒᵖ) (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W) :
      f.hom.app W (finiteRootProGenerator A m hm hA T W 1 z) = d.hom.app W z := by
    have h := congrArg (fun k ↦ k.hom.app W z)
      ((proLineHomEquiv T m hm A hA F).apply_symm_apply d')
    rw [proLineHomEquiv_generator] at h
    exact h
  refine ⟨f, ?_⟩
  intro W a z
  rw [proGenerator_smul, map_smul, h1]
  rfl

private theorem realizeLift (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (b : finiteSheaf T ell n 1 ⟶ fixedCoefficients T ell n (quotientLine T ell n 1)) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n 1) ⟶ quotientLine T ell n 1,
      ∀ W y, f.val.app W
        ((toSheafify (ProEt.topology T)
          ((finiteSheaf T ell n 1).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W y) =
        b.hom.app W y := by
  let P := (ProEtale.finiteCoefficientModulePresheaf T.ProEt
    (coefficient ell (n + 1))).obj (finiteSheaf T ell n 1).obj
  let g : P ⟶ (PresheafOfModules.restrictScalars (scalars T ell n)).obj
      (quotientLine T ell n 1).val :=
    { app := b.hom.app
      naturality := by
        intro U V v
        ext y
        exact ConcreteCategory.congr_hom (b.hom.naturality v) y }
  let f := (PresheafOfModules.sheafificationHomEquiv (scalars T ell n)).symm g
  have hf := (PresheafOfModules.sheafificationHomEquiv (scalars T ell n)).apply_symm_apply g
  have h := congrArg (fun k ↦ (PresheafOfModules.toPresheaf _).map k) hf
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h
  exact ⟨f, fun W y ↦ congrArg (fun k ↦ k.app W y) h⟩

/-- The first root line admits the normalized quotient comparison.

Source: smooth-purity transport, Step 2, quotient of the inverse-limit root line.
(blueprint: lem-pur-tate-tensor-generator-one)

Proof: insert the integral tensor unit by the natural additive map x ↦ 1 tensor x,
then apply the specified scalar-extension unit. The quotient coefficient sheaf is
annihilated by ell^(n+1), so this map kills the kernel of the epic root-tower
projection. Descend it to finite roots with Abelian.epiDesc. The finite-root Hom
equivalence extends this additive map to the finite coefficient tensor, and the
normalized finite-root site comparison gives the corresponding map from the
finite etale line pulled to the pro-etale site. Apply the realization
sheafification adjunction. Its unit identity, the normalized root comparison, and
the descent identity compute the result on every compatible root lift. Scalar
linearity gives scalars(a) tensor (1 tensor x), exactly the required formula.
The construction uses no choice of root basis and also applies to the empty
scheme. -/
theorem tateTensorQuotient_generator_one
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n 1) ⟶ quotientLine T ell n 1,
      GeneratorCompatible T ell n 1 f := by
  obtain ⟨d, hd⟩ := root_descends T ell hT n
  obtain ⟨g, hg⟩ := rootTensorLift T ell n d
  obtain ⟨sigma, _, _, hroot, htensor, _⟩ :=
    finiteRootSiteComparison (coefficient ell (n + 1))
  have hm : 0 < ell ^ (n + 1) := pow_pos (Fact.out : ell.Prime).pos _
  have hunit : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (n + 1)
  let b := (sigma (ell ^ (n + 1)) hm (CharP.cast_eq_zero _ _) T hunit).hom ≫ g
  obtain ⟨f, hf⟩ := realizeLift T ell n b
  refine ⟨f, ?_⟩
  intro U W v a z x hx
  simp only [one_smul, id_eq]
  rw [hf]
  change g.hom.app W
    ((sigma (ell ^ (n + 1)) hm (CharP.cast_eq_zero _ _) T hunit).hom.hom.app W _) = _
  simp only [finiteTateEtalePowerGenerator]
  erw [htensor, hg]
  have hz : (ProEtale.cartierRootsIso T (ell ^ (n + 1)) hm hunit).hom.hom.app W
      (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf (ell ^ (n + 1)))).obj.map v.op
          (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf (ell ^ (n + 1)))).hom.app U (z 0))) =
      (rootTowerProjection T ell n).hom.app W (x 0) := by
    have hinj : Function.Injective
        ((proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))).hom.app W) := by
      have : Mono (proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))) := by
        dsimp [proEtaleRootsOfUnityInclusion]
        infer_instance
      have : Mono (proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))).hom :=
        (sheafToPresheaf _ _).map_mono _
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hinj
    apply ULift.ext
    exact congrArg Additive.ofMul
      ((hroot _ hm T hunit U W v (z 0)).trans (hx 0).symm)
  rw [hz]
  have hd' := congrArg (fun k ↦ k.hom.app W (x 0)) hd
  change d.hom.app W ((rootTowerProjection T ell n).hom.app W (x 0)) =
    (rootIntoQuotient T ell n).hom.app W (x 0) at hd'
  rw [hd', rootIntoQuotient_apply]
  have hxgen : (fun _ : Fin 1 ↦ x 0) = x := by
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  rw [hxgen]
  simpa only [fixedCoefficients, pbcTensorSection, quotientLine, pbcExtend, reductionChange,
    mul_one] using
    (completedTensor_smul T (pbcAdicProjection T (datum.{u} ell) n)
      (integralLine T ell 1) W (((scalars T ell n).app W).hom a) 1
      (integralGenerator T ell W 1 x)).symm

end AlgebraicGeometry.Scheme.PurityIntegralTower
