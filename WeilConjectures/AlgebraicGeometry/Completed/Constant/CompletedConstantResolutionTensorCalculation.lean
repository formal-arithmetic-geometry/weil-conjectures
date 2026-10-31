/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRankOneComparison
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import WeilConjectures.Algebra.Homology.FlatScalarRealization
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Tensor calculation on finite-free completion resolutions

Source: Stacks Tags 06YN, 06YT, 06YU and 093M.
(blueprint: lem-weil-pbc-completed-constant-resolution-tensor-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private def tensorUnitComparison {K D : Type*} [Category* K] [Category* D]
    [MonoidalCategory D] (c : K ⥤ D) (k : K) (j : c.obj k ≅ 𝟙_ D) (P : D) :
    (c ⋙ MonoidalCategory.tensorRight P).obj k ≅ P :=
  (MonoidalCategory.tensorRight P).mapIso j ≪≫ MonoidalCategory.leftUnitor P


private theorem tensorUnitComparison_naturality
    {K D : Type*} [Category* K] [Category* D] [MonoidalCategory D]
    (c : K ⥤ D) (k : K) (j : c.obj k ≅ 𝟙_ D) {P Q : D} (f : P ⟶ Q) :
    c.obj k ◁ f ≫ (tensorUnitComparison c k j Q).hom =
      (tensorUnitComparison c k j P).hom ≫ f := by
  dsimp only [tensorUnitComparison, Iso.trans_hom, Functor.mapIso_hom]
  change c.obj k ◁ f ≫ j.hom ▷ Q ≫ (λ_ Q).hom =
    (j.hom ▷ P ≫ (λ_ P).hom) ≫ f
  simp only [Category.assoc]
  rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
    MonoidalCategory.leftUnitor_naturality]


-- A comparison can be normalized on the free rank-one module without choosing
-- coordinates in arbitrary modules. Naturality then fixes all its generators.
private def normalizedTensorIso {K D : Type*} [Category* K] [Category* D]
    [MonoidalCategory D] (c : K ⥤ D) (k : K) (j : c.obj k ≅ 𝟙_ D)
    (P : D) (G : K ⥤ D) (a : c ⋙ MonoidalCategory.tensorRight P ≅ G)
    (ρ : G.obj k ≅ P) : c ⋙ MonoidalCategory.tensorRight P ≅ G :=
  let δ := (tensorUnitComparison c k j P).symm ≪≫ a.app k ≪≫ ρ
  Functor.isoWhiskerLeft c
    ((MonoidalCategory.curriedTensor D).flip.mapIso δ.symm) ≪≫ a


private theorem normalizedTensorIso_unit
    {K D : Type*} [Category* K] [Category* D] [MonoidalCategory D]
    (c : K ⥤ D) (k : K) (j : c.obj k ≅ 𝟙_ D) (P : D) (G : K ⥤ D)
    (a : c ⋙ MonoidalCategory.tensorRight P ≅ G) (ρ : G.obj k ≅ P) :
    ((normalizedTensorIso c k j P G a ρ).app k).hom ≫ ρ.hom =
      (tensorUnitComparison c k j P).hom := by
  let δ := (tensorUnitComparison c k j P).symm ≪≫ a.app k ≪≫ ρ
  have hd : (a.app k).hom ≫ ρ.hom =
      (tensorUnitComparison c k j P).hom ≫ δ.hom := by
    simp [δ]
  change (c.obj k ◁ δ.inv ≫ (a.app k).hom) ≫ ρ.hom = _
  rw [Category.assoc, hd, ← Category.assoc, tensorUnitComparison_naturality, Category.assoc]
  simp


private def extensionCompIso (X : Scheme.{u})
    {R S V : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    completedConstantExtension X a ⋙ completedConstantExtension X b ≅
      completedConstantExtension X (a ≫ b) := by
  let aa := (completedAdjunction X a).choose
  let ab := (completedAdjunction X b).choose
  let ac := (completedAdjunction X (a ≫ b)).choose
  exact ((aa.comp ab).ofNatIsoRight (completedRestrictCompIso X a b).symm).leftAdjointUniq ac


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def constantScalarChangeIso (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D) :
    adicLisseConstantModules X B ⋙ completedConstantExtension X
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q)) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙ adicLisseConstantModules X D := by
  let J := ProEt.topology X
  let a := (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  let ac := (completedAdjunction X a).choose
  let ad := ConstantScalarRealization.adjunction J q
  let z := ac.leftAdjointUniq ad
  haveI (M : ModuleCat.{u + 1} B) :
      IsIso (ConstantScalarRealization.moduleComparison J q M) :=
    (ConstantScalarRealization.moduleComparison_tensor J q M).1
  let e : commutativeSiteConstantModuleFunctor J B ⋙
      ConstantScalarRealization.extension J q ≅
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙
          commutativeSiteConstantModuleFunctor J D :=
    NatIso.ofComponents (fun M ↦
      asIso (ConstantScalarRealization.moduleComparison J q M))
      (fun f ↦ ConstantScalarRealization.moduleComparison_naturality J q f)
  exact Functor.isoWhiskerLeft (adicLisseConstantModules X B) z ≪≫ e


private def restrictedTensorIso {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (U : C ⥤ D) [U.Monoidal] (N : C) :
    U ⋙ MonoidalCategory.tensorRight (U.obj N) ≅ MonoidalCategory.tensorRight N ⋙ U := by
  refine NatIso.ofComponents (fun M ↦ Functor.Monoidal.μIso U M N) ?_
  intro M M' f
  exact Functor.LaxMonoidal.μ_natural_left U f N


private theorem reduction_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I (n + 1)).comp
        (AdicCompletion.evalₐ I (n + 2)).toRingHom =
      (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs


private def scalarReductionMap
    {B D E : Type (u + 1)} [CommRing B] [CommRing D] [CommRing E]
    (f : B →+* D) (g : B →+* E) (q : D →+* E) (hq : q.comp f = g)
    (M : ModuleCat.{u + 1} B) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj M →ₛₗ[q]
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M := by
  let N := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M
  letI : Module B D := Module.compHom D f
  letI : Module B E := Module.compHom E g
  letI : Module B N := Module.compHom N g
  letI : SMulCommClass B D D := ModuleCat.sMulCommClass_mk f D
  letI : SMulCommClass B E E := ModuleCat.sMulCommClass_mk g E
  let k : D →ₗ[B] M →ₗ[B] N :=
    { toFun := fun d ↦
        { toFun := fun x ↦ q d ⊗ₜ[B, g] x
          map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
          map_smul' := fun b x ↦ by
            change q d ⊗ₜ[B, g] (b • x) = g b • (q d ⊗ₜ[B, g] x)
            change q d ⊗ₜ[B, g] (b • x) = (g b * q d) ⊗ₜ[B, g] x
            exact (TensorProduct.smul_tmul (R := B) b (q d) x).symm }
      map_add' := by
        intro d d'
        ext x
        exact (congrArg (fun z ↦ z ⊗ₜ[B, g] x) (map_add q d d')).trans
          (TensorProduct.add_tmul _ _ _)
      map_smul' := by
        intro b d
        ext x
        change q (f b * d) ⊗ₜ[B, g] x = g b • (q d ⊗ₜ[B, g] x)
        rw [map_mul, show q (f b) = g b from RingHom.congr_fun hq b]
        rfl }
  let t := TensorProduct.lift k
  refine
    { toFun := t
      map_add' := t.map_add
      map_smul' := ?_ }
  change ∀ (d : D) (z : TensorProduct B D M), t (d • z) = q d • t z
  intro d z
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul d' x =>
    change q (d * d') ⊗ₜ[B, g] x = (q d * q d') ⊗ₜ[B, g] x
    rw [map_mul]


private theorem scalarReductionMap_naturality
    {B D E : Type (u + 1)} [CommRing B] [CommRing D] [CommRing E]
    (f : B →+* D) (g : B →+* E) (q : D →+* E) (hq : q.comp f = g)
    {M N : ModuleCat.{u + 1} B} (l : M ⟶ N) :
    ∀ z : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj M,
      scalarReductionMap f g q hq N
          (((ModuleCat.extendScalars f).map l).hom z) =
        ((ModuleCat.extendScalars g).map l).hom (scalarReductionMap f g q hq M z) := by
  let : Module B D := Module.compHom D f
  change ∀ z : TensorProduct B D M, _
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p x => rfl


private theorem extension_span_one
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (M : ModuleCat.{u + 1} B) (p : D) (x : M) :
    (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton B M x) : ModuleCat.of B B ⟶ M)).hom)
        (p ⊗ₜ[B,q] 1) = (p ⊗ₜ[B,q] x : (ModuleCat.extendScalars q).obj M) := by
  change p ⊗ₜ[B,q] ((1 : B) • x) = p ⊗ₜ[B,q] x
  rw [one_smul]


private theorem scalarReductionMap_tmul
    {B D E : Type (u + 1)} [CommRing B] [CommRing D] [CommRing E]
    (f : B →+* D) (g : B →+* E) (q : D →+* E) (hq : q.comp f = g)
    (M : ModuleCat.{u + 1} B) (d : D) (x : M) :
    scalarReductionMap f g q hq M (d ⊗ₜ[B, f] x) = q d ⊗ₜ[B, g] x := rfl


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def constantSemilinear (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (f : M →ₛₗ[q] N) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X B).obj M) ⟶
    (SheafOfModules.restrictScalars ((adicLisseForget X).map b)).obj
      ((adicLisseConstantModules X D).obj N) := by
  let k := CompletedConstantProjection.constantMap X q (𝟙 _)
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q))
    (Category.id_comp _) M N f
  refine ⟨{
    app := fun U ↦ ModuleCat.ofHom
      (X := ((SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
        ((adicLisseConstantModules X B).obj M)).val.obj U)
      (Y := ((SheafOfModules.restrictScalars ((adicLisseForget X).map b)).obj
        ((adicLisseConstantModules X D).obj N)).val.obj U)
      { toFun := k.val.app U
        map_add' := map_add _
        map_smul' := ?_ }
    naturality := ?_ }⟩
  · intro r x
    let x' : ((adicLisseConstantModules X B).obj M).val.obj _ := x
    let y' : ((adicLisseConstantModules X D).obj N).val.obj _ := k.val.app _ x'
    change k.val.app _ (a.hom.app _ r • x') = b.hom.app _ r • y'
    have hk := (k.val.app _).hom.map_smul (a.hom.app _ r) x'
    change k.val.app _ (a.hom.app _ r • x') =
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q)).hom.app _ (a.hom.app _ r) • y' at hk
    rw [hk]
    congr 1
    exact congrArg (fun z ↦ z.hom.app _ r) hab
  · intro U V g
    ext x
    exact PresheafOfModules.naturality_apply k.val g x


private theorem constantSemilinear_generator (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (f : M →ₛₗ[q] N)
    (U : X.ProEtᵒᵖ) (x : M) :
    (constantSemilinear X q R a b hab M N f).val.app U
      (completedConstantGenerator X B M U x) = completedConstantGenerator X D N U (f x) := by
  exact CompletedConstantProjection.constantMap_generator X q (𝟙 _)
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q))
    (Category.id_comp _) M N f U x


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem constant_generator_hom_ext (X : Scheme.{u})
    {B : Type (u + 1)} [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (M : ModuleCat.{u + 1} B)
    (N : completedConstantModules X R)
    (f g : (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X B).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M),
      f.val.app U (completedConstantGenerator X B M U x) =
        g.val.app U (completedConstantGenerator X B M U x)) : f = g := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _ N.isSheaf
  ext U x
  exact h U x


private theorem constantSemilinear_naturality (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M M' : ModuleCat.{u + 1} B) (N N' : ModuleCat.{u + 1} D)
    (f : M →ₛₗ[q] N) (f' : M' →ₛₗ[q] N') (g : M ⟶ M') (k : N ⟶ N')
    (h : ∀ x : M, f' (g.hom x) = k.hom (f x)) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).map
        ((adicLisseConstantModules X B).map g) ≫
        constantSemilinear X q R a b hab M' N' f' =
      constantSemilinear X q R a b hab M N f ≫
        (SheafOfModules.restrictScalars ((adicLisseForget X).map b)).map
          ((adicLisseConstantModules X D).map k) := by
  apply constant_generator_hom_ext X R a M _
  intro U x
  change (constantSemilinear X q R a b hab M' N' f').val.app U
    (((adicLisseConstantModules X B).map g).val.app U
      (completedConstantGenerator X B M U x)) =
    ((adicLisseConstantModules X D).map k).val.app U
      ((constantSemilinear X q R a b hab M N f).val.app U
        (completedConstantGenerator X B M U x))
  rw [CompletedConstantProjection.constant_map_generator,
    constantSemilinear_generator, constantSemilinear_generator,
    CompletedConstantProjection.constant_map_generator]
  exact congrArg (completedConstantGenerator X D N' U) (h x)


-- Work with the unbundled tensor carrier, so scalar restriction is unfolded once.
set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem tensor_constant_generator_hom_ext (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X D) (M : ModuleCat.{u + 1} B)
    (N : completedConstantModules X R)
    (f g : (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X D).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q).obj M)) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (p : D) (x : M),
      f.val.app U (completedConstantGenerator X D _ U (p ⊗ₜ[B,q] x)) =
        g.val.app U (completedConstantGenerator X D _ U (p ⊗ₜ[B,q] x))) : f = g := by
  apply constant_generator_hom_ext X R a _ N
  intro U z
  let : Module B D := Module.compHom D q
  let η := ((toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of ((ModuleCat.extendScalars q).obj M)))).app U).hom
  let l : TensorProduct B D M →+ N.val.obj U :=
    (f.val.app U).hom.toAddMonoidHom.comp η
  let r : TensorProduct B D M →+ N.val.obj U :=
    (g.val.app U).hom.toAddMonoidHom.comp η
  change l z = r z
  suffices hz : ∀ z : TensorProduct B D M, l z = r z from hz z
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p x => exact h U p x


private abbrev reductionModuleLevel (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom ⋙
      adicLisseConstantModules X (A ⧸ I ^ (n + 1)) ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map
          (β ≫ limit.π (adicLisseRingSystem X I) (op n)))


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionModuleIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    c ⋙ MonoidalCategory.tensorRight (P.diagram.obj (op n)) ≅
      reductionModuleLevel X I R β n := by
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesMonoidal (adicLisseCompletedRing X I)
  let := HasDerivedCategory.standard (completedConstantModules X R)
  let := HasDerivedCategory.standard
    (completedConstantModules X (adicLisseCompletedRing X I))
  let tr := (SheafOfModules.ringIso_tensor_transport (asIso β)).some
  let U := SheafOfModules.restrictScalars ((adicLisseForget X).map β)
  letI : U.Braided := tr.monoidal
  let π := limit.π (adicLisseRingSystem X I) (op n)
  let V := completedRestriction X π
  let N := SheafOfModules.unit ((adicLisseForget X).obj
    ((adicLisseRingSystem X I).obj (op n)))
  let ep : U.obj (V.obj N) ≅ P.diagram.obj (op n) :=
    ((completedRestrictCompIso X β π).app N).symm ≪≫ (eqToIso (P.level (op n))).symm
  let C := adicLisseConstantModules X (AdicCompletion I A)
  let E := completedConstantExtension X d.scalar
  let a := Functor.isoWhiskerLeft c
    ((MonoidalCategory.curriedTensor (completedConstantModules X R)).flip.mapIso ep.symm)
  let b := Functor.isoWhiskerRight e (MonoidalCategory.tensorRight (U.obj (V.obj N)))
  let k := Functor.isoWhiskerLeft E (restrictedTensorIso U (V.obj N))
  let t := (completedOrdinaryRestrictionComparison X π).some
  let l := Functor.isoWhiskerRight (Functor.isoWhiskerLeft E t.symm) U
  let m := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft C (extensionCompIso X d.scalar π)) (V ⋙ U)
  let z := eqToIso (congrArg (completedConstantExtension X) (d.scalar_projection n))
  let o := Functor.isoWhiskerRight (Functor.isoWhiskerLeft C z) (V ⋙ U)
  let q := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let p := Functor.isoWhiskerRight (constantScalarChangeIso X q) (V ⋙ U)
  let r := Functor.isoWhiskerLeft
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙ adicLisseConstantModules X (A ⧸ I ^ (n + 1)))
    (completedRestrictCompIso X β π).symm
  exact a ≪≫ b ≪≫ Functor.isoWhiskerLeft C k ≪≫
    Functor.isoWhiskerLeft C l ≪≫ m ≪≫ o ≪≫ p ≪≫ r


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def scalarRegularIso {B D : Type (u + 1)} [CommRing B] [CommRing D]
    (q : B →+* D) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q).obj (ModuleCat.of B B) ≅
      ModuleCat.of D D := by
  letI := q.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid B D D).toModuleIso


private theorem regular_constant_generator_hom_ext (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X D) (N : completedConstantModules X R)
    (f g : (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X D).obj ((ModuleCat.extendScalars q).obj
        (ModuleCat.of B B))) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (p : D),
      f.val.app U (completedConstantGenerator X D _ U (p ⊗ₜ[B,q] 1)) =
        g.val.app U (completedConstantGenerator X D _ U (p ⊗ₜ[B,q] 1))) : f = g := by
  let F := adicLisseConstantModules X D ⋙
    SheafOfModules.restrictScalars ((adicLisseForget X).map a)
  let e := F.mapIso (scalarRegularIso q).symm
  apply (cancel_epi e.hom).mp
  apply constant_generator_hom_ext X R a (ModuleCat.of D D) N
  intro U p
  change f.val.app U
    (((adicLisseConstantModules X D).map (scalarRegularIso q).inv).val.app U
      (completedConstantGenerator X D (ModuleCat.of D D) U p)) =
    g.val.app U
      (((adicLisseConstantModules X D).map (scalarRegularIso q).inv).val.app U
        (completedConstantGenerator X D (ModuleCat.of D D) U p))
  rw [CompletedConstantProjection.constant_map_generator]
  exact h U p


private def reductionRegularIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :
    (reductionModuleLevel X I R β n).obj
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) ≅
      completedConstantQuotient X I R β (op n) := by
  let q := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let B := A ⧸ I ^ (n + 1)
  haveI := CompletedConstantRankOne.constantUnit_isIso X B
  exact (SheafOfModules.restrictScalars ((adicLisseForget X).map
    (β ≫ limit.π (adicLisseRingSystem X I) (op n)))).mapIso
      ((adicLisseConstantModules X B).mapIso (scalarRegularIso q) ≪≫
        asIso (CompletedConstantRankOne.constantUnit X B))


set_option maxHeartbeats 2000000 in
-- Comparing the several bundled scalar-restriction presentations is expensive.
private theorem reductionRegularIso_generator (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) (U : X.ProEtᵒᵖ)
    (p : A ⧸ I ^ (n + 1)) (x : AdicCompletion I A) :
    (reductionRegularIso X I R β n).hom.val.app U
      (completedConstantGenerator X _ _ U
        (p ⊗ₜ[AdicCompletion I A, (AdicCompletion.evalₐ I (n + 1)).toRingHom] x)) =
      (adicLisseConstantUnit X (A ⧸ I ^ (n + 1))).app U
        (AdicCompletion.evalₐ I (n + 1) x * p) := by
  let B := A ⧸ I ^ (n + 1)
  let q := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  change (CompletedConstantRankOne.constantUnit X B).val.app U
    (((adicLisseConstantModules X B).map (scalarRegularIso q).hom).val.app U
      (completedConstantGenerator X B ((ModuleCat.extendScalars q).obj
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A))) U
          (p ⊗ₜ[AdicCompletion I A, q] x))) = _
  rw [CompletedConstantProjection.constant_map_generator,
    CompletedConstantRankOne.constantUnit_generator]
  rfl


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def realizationUnitIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β)) :
    letI := SheafOfModules.cochainModulesMonoidal R
    c.obj (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) ≅
      𝟙_ (completedConstantModules X R) := by
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesMonoidal (adicLisseCompletedRing X I)
  let := HasDerivedCategory.standard (completedConstantModules X R)
  let := HasDerivedCategory.standard
    (completedConstantModules X (adicLisseCompletedRing X I))
  let tr := (SheafOfModules.ringIso_tensor_transport (asIso β)).some
  let U := SheafOfModules.restrictScalars ((adicLisseForget X).map β)
  letI : U.Braided := tr.monoidal
  exact e.app _ ≪≫ U.mapIso (CompletedConstantReduction.constantChange_unit X d.scalar) ≪≫
    (Functor.Monoidal.εIso U).symm


private theorem reduction_projection_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1))) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) =
      β ≫ limit.π (adicLisseRingSystem X I) (op n) := by
  rw [Category.assoc]
  have hw := limit.w (adicLisseRingSystem X I) (homOfLE (Nat.le_succ n)).op
  dsimp only [adicLisseRingSystem] at hw
  rw [Functor.ofOpSequence_map_homOfLE_succ] at hw
  exact congrArg (β ≫ ·) hw


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionModuleStep (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :
    reductionModuleLevel X I R β (n + 1) ⟶ reductionModuleLevel X I R β n where
  app M := constantSemilinear X (Ideal.Quotient.factorPowSucc I (n + 1)) R
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
    (β ≫ limit.π (adicLisseRingSystem X I) (op n))
    (reduction_projection_step X I R β n)
    _ _ (scalarReductionMap _ _ _ (reduction_eval_step I n) M)
  naturality := by
    intro M N f
    exact constantSemilinear_naturality X (Ideal.Quotient.factorPowSucc I (n + 1)) R
      (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
      (β ≫ limit.π (adicLisseRingSystem X I) (op n))
      (reduction_projection_step X I R β n) _ _ _ _
      (scalarReductionMap _ _ _ (reduction_eval_step I n) M)
      (scalarReductionMap _ _ _ (reduction_eval_step I n) N)
      ((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 2)).toRingHom).map f)
      ((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 1)).toRingHom).map f)
      (scalarReductionMap_naturality _ _ _ (reduction_eval_step I n) f)


private theorem reductionModuleStep_generator (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (M : ModuleCat.{u + 1} (AdicCompletion I A)) (U : X.ProEtᵒᵖ)
    (p : A ⧸ I ^ (n + 2)) (x : M) :
    ((reductionModuleStep X I R β n).app M).val.app U
      (completedConstantGenerator X _ _ U
        (p ⊗ₜ[AdicCompletion I A, (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) =
      completedConstantGenerator X _ _ U
        (Ideal.Quotient.factorPowSucc I (n + 1) p ⊗ₜ[AdicCompletion I A,
          (AdicCompletion.evalₐ I (n + 1)).toRingHom] x) := by
  exact constantSemilinear_generator X (Ideal.Quotient.factorPowSucc I (n + 1)) R
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
    (β ≫ limit.π (adicLisseRingSystem X I) (op n))
    (reduction_projection_step X I R β n) _ _
    (scalarReductionMap _ _ _ (reduction_eval_step I n) M) U _


set_option maxHeartbeats 1000000 in
-- The comparison uses the regular scalar-extension isomorphism on its source.
private theorem reductionRegularIso_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    (reductionModuleStep X I R β n).app
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) ≫
        (reductionRegularIso X I R β n).hom =
      (reductionRegularIso X I R β (n + 1)).hom ≫
        eqToHom (P.level (op (n + 1))).symm ≫
        P.diagram.map (homOfLE (Nat.le_succ n)).op ≫ eqToHom (P.level (op n)) := by
  apply regular_constant_generator_hom_ext X
    (AdicCompletion.evalₐ I (n + 2)).toRingHom R
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1))) _
  intro U p
  change (reductionRegularIso X I R β n).hom.val.app U
    (((reductionModuleStep X I R β n).app _).val.app U
      (completedConstantGenerator X _ _ U _)) =
    ((eqToHom (P.level (op (n + 1))).symm ≫
      P.diagram.map (homOfLE (Nat.le_succ n)).op ≫
        eqToHom (P.level (op n))).val.app U)
      ((reductionRegularIso X I R β (n + 1)).hom.val.app U
        (completedConstantGenerator X _ _ U _))
  rw [reductionModuleStep_generator X I R β n _ U p 1]
  rw [reductionRegularIso_generator X I R β n U
    (Ideal.Quotient.factorPowSucc I (n + 1) p) 1]
  rw [reductionRegularIso_generator X I R β (n + 1) U p 1]
  simp only [map_one, one_mul]
  rw [P.transition (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op U]
  dsimp only [adicLisseRingSystem]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact (CompletedConstantRankOne.ringMap_unit X
    (Ideal.Quotient.factorPowSucc I (n + 1)) U p).symm


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem reduction_regular_hom_ext (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (M : ModuleCat.{u + 1} (AdicCompletion I A)) (N : completedConstantModules X R)
    (f g : (reductionModuleLevel X I R β n).obj M ⟶ N)
    (h : ∀ x : M,
      (reductionModuleLevel X I R β n).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton (AdicCompletion I A) M x)) ≫ f =
        (reductionModuleLevel X I R β n).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton (AdicCompletion I A) M x)) ≫ g) :
    f = g := by
  apply tensor_constant_generator_hom_ext X
    (AdicCompletion.evalₐ I (n + 1)).toRingHom R
    (β ≫ limit.π (adicLisseRingSystem X I) (op n)) _ _
  intro U p x
  let t : ModuleCat.of (AdicCompletion I A) (AdicCompletion I A) ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton (AdicCompletion I A) M x)
  let q := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let z := (p ⊗ₜ[AdicCompletion I A,q] 1 :
    (ModuleCat.extendScalars q).obj (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)))
  have hgen : ((reductionModuleLevel X I R β n).map t).val.app U
      (completedConstantGenerator X _ _ U z) =
        completedConstantGenerator X _ ((ModuleCat.extendScalars q).obj M) U
          (p ⊗ₜ[AdicCompletion I A,q] x) :=
    (CompletedConstantProjection.constant_map_generator X
      ((ModuleCat.extendScalars q).map t) U z).trans
        (congrArg (completedConstantGenerator X _ ((ModuleCat.extendScalars q).obj M) U)
          (extension_span_one q M p x))
  have hx := congrArg (fun k ↦ k.val.app U
    (completedConstantGenerator X _ _ U z)) (h x)
  change f.val.app U (((reductionModuleLevel X I R β n).map t).val.app U
    (completedConstantGenerator X _ _ U z)) =
    g.val.app U (((reductionModuleLevel X I R β n).map t).val.app U
      (completedConstantGenerator X _ _ U z)) at hx
  rw [hgen] at hx
  exact hx


private theorem reduction_natTrans_ext (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (H : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (a b : reductionModuleLevel X I R β n ⟶ H)
    (h : a.app (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) =
      b.app (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A))) : a = b := by
  apply NatTrans.ext
  funext M
  apply reduction_regular_hom_ext X I R β n M _
  intro x
  rw [a.naturality, b.naturality, h]


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem normalizedTensorIso_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (P : CompletedConstantQuotientTower X I R β)
    (j : c.obj (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) ≅
      SheafOfModules.unit ((adicLisseForget X).obj R))
    (a : ∀ n : ℕ, letI := SheafOfModules.cochainModulesMonoidal R
      c ⋙ MonoidalCategory.tensorRight (P.diagram.obj (op n)) ≅
        reductionModuleLevel X I R β n) (n : ℕ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    let b := fun n ↦ normalizedTensorIso c
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) j
      (P.diagram.obj (op n)) (reductionModuleLevel X I R β n) (a n)
      (reductionRegularIso X I R β n ≪≫ (eqToIso (P.level (op n))).symm)
    Functor.whiskerLeft c ((MonoidalCategory.curriedTensor _).flip.map
        (P.diagram.map (homOfLE (Nat.le_succ n)).op)) ≫ (b n).hom =
      (b (n + 1)).hom ≫ reductionModuleStep X I R β n := by
  let := SheafOfModules.cochainModulesMonoidal R
  let k := ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)
  let ρ := fun n ↦ reductionRegularIso X I R β n ≪≫ (eqToIso (P.level (op n))).symm
  let b := fun n ↦ normalizedTensorIso c k j (P.diagram.obj (op n))
    (reductionModuleLevel X I R β n) (a n) (ρ n)
  let f := P.diagram.map (homOfLE (Nat.le_succ n)).op
  let t := Functor.whiskerLeft c ((MonoidalCategory.curriedTensor _).flip.map f)
  have hρ : (reductionModuleStep X I R β n).app k ≫ (ρ n).hom =
      (ρ (n + 1)).hom ≫ f := by
    dsimp only [ρ, Iso.trans_hom, eqToIso.inv, Iso.symm_hom]
    rw [← Category.assoc, reductionRegularIso_step X I R β P n]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  have hb (m : ℕ) : (b m).hom.app k ≫ (ρ m).hom =
      (tensorUnitComparison c k j (P.diagram.obj (op m))).hom :=
    normalizedTensorIso_unit c k j _ _ (a m) (ρ m)
  have hinv : (b (n + 1)).inv.app k ≫
      (tensorUnitComparison c k j (P.diagram.obj (op (n + 1)))).hom =
        (ρ (n + 1)).hom := by
    rw [← hb (n + 1), ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have he : (b (n + 1)).inv ≫ t ≫ (b n).hom = reductionModuleStep X I R β n := by
    apply reduction_natTrans_ext X I R β (n + 1) _
    apply (cancel_mono (ρ n).hom).mp
    change ((b (n + 1)).inv.app k ≫ (c.obj k ◁ f) ≫
        (b n).hom.app k) ≫ (ρ n).hom = _
    simp only [Category.assoc]
    rw [hb, tensorUnitComparison_naturality, ← Category.assoc, hinv]
    exact hρ.symm
  apply (cancel_epi (b (n + 1)).inv).mp
  change (b (n + 1)).inv ≫ (t ≫ (b n).hom) =
    (b (n + 1)).inv ≫ ((b (n + 1)).hom ≫ reductionModuleStep X I R β n)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using he


set_option maxHeartbeats 1000000 in
-- Cache the complex diagram once for the tower and its comparison.
private def reductionComplexDiagram (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    ℕᵒᵖ ⥤ (CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ) := by
  have hL (n : ℕ) : (reductionModuleLevel X I R β n).Additive := by
    let := h n
    let := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
    infer_instance
  letI (n : ℕ) : (reductionModuleLevel X I R β n).Additive := hL n
  exact Functor.ofOpSequence
    (X := fun n ↦ (reductionModuleLevel X I R β n).mapHomologicalComplex (.up ℤ))
    (fun n ↦ NatTrans.mapHomologicalComplex (reductionModuleStep X I R β n) (.up ℤ))


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    CompletedConstantReductionTower X I R β h := by
  let F := reductionComplexDiagram X I R β h
  refine
    { functor := F.flip
      level := fun _ _ ↦ rfl
      map_level := fun _ _ _ _ ↦ ?_
      transition := ?_ }
  · dsimp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro M n i U p x
    dsimp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (((F.map (homOfLE (Nat.le_succ n)).op).app M).f i).val.app U
      (completedConstantGenerator X _ _ U (p ⊗ₜ[AdicCompletion I A,
        (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) = _
    dsimp only [F, reductionComplexDiagram]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact reductionModuleStep_generator X I R β n (M.X i) U p x


private theorem reductionTower_functor (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    (reductionTower X I R β h).functor = (reductionComplexDiagram X I R β h).flip := rfl

attribute [local irreducible] reductionTower


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def singleTensorFunctorIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (N : completedConstantModules X R) :
    letI := SheafOfModules.cochainModulesMonoidal R
    (completedConstantTensor X R).flip.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ≅
      (MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ) := by
  let := SheafOfModules.cochainModulesMonoidal R
  exact NatIso.ofComponents (fun K ↦
    CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor _) N K)
    (fun f ↦ CochainComplex.mapBifunctorSingle₂Iso_hom_naturality
      (MonoidalCategory.curriedTensor _) N f)


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem singleTensorFunctorIso_coefficient (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {N N' : completedConstantModules X R} (f : N ⟶ N')
    (K : CochainComplex (completedConstantModules X R) ℤ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    ((completedConstantTensor X R).flip.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map f)).app K ≫
        (singleTensorFunctorIso X R N').hom.app K =
      (singleTensorFunctorIso X R N).hom.app K ≫
        (NatTrans.mapHomologicalComplex
          ((MonoidalCategory.curriedTensor _).flip.map f) (.up ℤ)).app K := by
  let := SheafOfModules.cochainModulesMonoidal R
  apply (cancel_epi ((singleTensorFunctorIso X R N).inv.app K)).mp
  apply (cancel_mono ((singleTensorFunctorIso X R N').inv.app K)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  exact (CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂
    (MonoidalCategory.curriedTensor _) f K).symm


-- Lift the comparison while its functors and isomorphisms are still abstract.
private def liftComparisonIso {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (c : C ⥤ D) [c.Additive]
    {G : D ⥤ D} [G.Additive] {H : C ⥤ D} [H.Additive]
    {T : CochainComplex D ℤ ⥤ CochainComplex D ℤ}
    (s : T ≅ G.mapHomologicalComplex (.up ℤ)) (a : c ⋙ G ≅ H) :
    c.mapHomologicalComplex (.up ℤ) ⋙ T ≅ H.mapHomologicalComplex (.up ℤ) :=
  Functor.isoWhiskerLeft (c.mapHomologicalComplex (.up ℤ)) s ≪≫
    Functor.mapHomologicalComplexCompIso a (.up ℤ)

private theorem liftComparisonIso_step {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (c : C ⥤ D) [c.Additive]
    {G₀ G₁ : D ⥤ D} [G₀.Additive] [G₁.Additive]
    {H₀ H₁ : C ⥤ D} [H₀.Additive] [H₁.Additive]
    {T₀ T₁ : CochainComplex D ℤ ⥤ CochainComplex D ℤ}
    (s₀ : T₀ ≅ G₀.mapHomologicalComplex (.up ℤ))
    (s₁ : T₁ ≅ G₁.mapHomologicalComplex (.up ℤ))
    (a₀ : c ⋙ G₀ ≅ H₀) (a₁ : c ⋙ G₁ ≅ H₁)
    (t : T₁ ⟶ T₀) (f : G₁ ⟶ G₀) (g : H₁ ⟶ H₀)
    (ht : ∀ K, t.app K ≫ s₀.hom.app K =
      s₁.hom.app K ≫ (NatTrans.mapHomologicalComplex f (.up ℤ)).app K)
    (ha : Functor.whiskerLeft c f ≫ a₀.hom = a₁.hom ≫ g)
    (F : CochainComplex C ℤ) :
    t.app ((c.mapHomologicalComplex (.up ℤ)).obj F) ≫
        (liftComparisonIso c s₀ a₀).hom.app F =
      (liftComparisonIso c s₁ a₁).hom.app F ≫
        (NatTrans.mapHomologicalComplex g (.up ℤ)).app F := by
  dsimp only [liftComparisonIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app]
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  apply congrArg (s₁.hom.app ((c.mapHomologicalComplex (.up ℤ)).obj F) ≫ ·)
  apply HomologicalComplex.hom_ext
  intro i
  exact congrArg (fun z ↦ z.app (F.X i)) ha

attribute [local irreducible] liftComparisonIso


private def isoOfOpSequence {D : Type*} [Category* D] {F G : ℕᵒᵖ ⥤ D}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (h : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op) : F ≅ G :=
  NatIso.ofComponents (fun n ↦ e n.unop)
    (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (e n).hom) h).naturality f)


set_option maxHeartbeats 1000000 in
-- Name the normalized module comparison before lifting it to complexes.
private def reductionNormalizedModuleIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    c ⋙ MonoidalCategory.tensorRight (P.diagram.obj (op n)) ≅
      reductionModuleLevel X I R β n := by
  let := SheafOfModules.cochainModulesMonoidal R
  exact normalizedTensorIso c
    (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A))
    (realizationUnitIso X I d R β c e) (P.diagram.obj (op n))
    (reductionModuleLevel X I R β n) (reductionModuleIso X I d R β c e P n)
    (reductionRegularIso X I R β n ≪≫ (eqToIso (P.level (op n))).symm)


set_option maxHeartbeats 1000000 in
-- Check module transition compatibility independently of the cochain construction.
private theorem reductionNormalizedModuleIso_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    Functor.whiskerLeft c ((MonoidalCategory.curriedTensor _).flip.map
        (P.diagram.map (homOfLE (Nat.le_succ n)).op)) ≫
        (reductionNormalizedModuleIso X I d R β c e P n).hom =
      (reductionNormalizedModuleIso X I d R β c e P (n + 1)).hom ≫
        reductionModuleStep X I R β n := by
  exact normalizedTensorIso_step X I R β c P
    (realizationUnitIso X I d R β c e) (reductionModuleIso X I d R β c e P) n


set_option maxHeartbeats 1000000 in
-- Keep the level isomorphism as a named term for kernel checking.
private def reductionComplexLevelIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive)
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    completedConstantMapComplex c hc ⋙
        (completedConstantTensor X R).flip.obj
          ((HomologicalComplex.single _ (.up ℤ) 0).obj (P.diagram.obj (op n))) ≅
      (reductionComplexDiagram X I R β h).obj (op n) := by
  let := hc
  let := h n
  let := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
  let := SheafOfModules.cochainModulesMonoidal R
  exact liftComparisonIso c (singleTensorFunctorIso X R (P.diagram.obj (op n)))
    (reductionNormalizedModuleIso X I d R β c e P n)

set_option maxHeartbeats 1000000 in
-- Check the complex successor square before assembling a sequence isomorphism.
private theorem reductionComplexLevelIso_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive)
    (P : CompletedConstantQuotientTower X I R β)
    (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ) (n : ℕ) :
    ((completedConstantTensor X R).flip.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (P.diagram.map (homOfLE (Nat.le_succ n)).op))).app
            ((completedConstantMapComplex c hc).obj F) ≫
        (reductionComplexLevelIso X I d R β c hc e h P n).hom.app F =
      (reductionComplexLevelIso X I d R β c hc e h P (n + 1)).hom.app F ≫
        ((reductionComplexDiagram X I R β h).map
          (homOfLE (Nat.le_succ n)).op).app F := by
  let := hc
  let := h n
  let := h (n + 1)
  let := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
  let := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 2)).toRingHom).isLeftAdjoint
  let := SheafOfModules.cochainModulesMonoidal R
  have hmap : ((reductionComplexDiagram X I R β h).map
      (homOfLE (Nat.le_succ n)).op).app F =
        (NatTrans.mapHomologicalComplex (reductionModuleStep X I R β n) (.up ℤ)).app F := by
    dsimp only [reductionComplexDiagram]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  rw [hmap]
  exact liftComparisonIso_step c
    (singleTensorFunctorIso X R (P.diagram.obj (op n)))
    (singleTensorFunctorIso X R (P.diagram.obj (op (n + 1))))
    (reductionNormalizedModuleIso X I d R β c e P n)
    (reductionNormalizedModuleIso X I d R β c e P (n + 1))
    ((completedConstantTensor X R).flip.map
      ((HomologicalComplex.single _ (.up ℤ) 0).map
        (P.diagram.map (homOfLE (Nat.le_succ n)).op)))
    ((MonoidalCategory.curriedTensor _).flip.map
      (P.diagram.map (homOfLE (Nat.le_succ n)).op))
    (reductionModuleStep X I R β n)
    (singleTensorFunctorIso_coefficient X R _)
    (reductionNormalizedModuleIso_step X I d R β c e P n) F



set_option maxHeartbeats 1000000 in
-- Assemble the already checked components through a generic sequence constructor.
private def resolutionTowerIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive)
    (P : CompletedConstantQuotientTower X I R β) :
    completedConstantMapComplex c hc ⋙
        (P.diagram ⋙ HomologicalComplex.single _ (.up ℤ) 0 ⋙
          (completedConstantTensor X R).flip).flip ≅
      (reductionTower X I R β h).functor := by
  rw [reductionTower_functor]
  refine NatIso.ofComponents (fun F ↦ isoOfOpSequence
    (fun n ↦ (reductionComplexLevelIso X I d R β c hc e h P n).app F)
    (reductionComplexLevelIso_step X I d R β c hc e h P F)) ?_
  intro F F' f
  apply NatTrans.ext
  funext n
  exact (reductionComplexLevelIso X I d R β c hc e h P n.unop).hom.naturality f

set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem flatOnSite_of_iso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N : completedConstantModules X R} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) N := by
  let := SheafOfModules.cochainModulesMonoidal R
  let k := SheafOfModules.siteSheafTensorRightIso R M ≪≫
    (MonoidalCategory.curriedTensor _).flip.mapIso e ≪≫
      (SheafOfModules.siteSheafTensorRightIso R N).symm
  exact (exactFunctor _ _).prop_of_iso k hM


set_option maxHeartbeats 1000000 in
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem realized_resolution_kflat (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (r : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((completedConstantMapComplex c hc).obj r.obj.left) := by
  let := hc
  let := HasDerivedCategory.standard (completedConstantModules X R)
  let := HasDerivedCategory.standard
    (completedConstantModules X (adicLisseCompletedRing X I))
  let tr := (SheafOfModules.ringIso_tensor_transport (asIso β)).some
  obtain ⟨b, hb⟩ := r.property.2.2.2
  have : r.obj.left.IsStrictlyLE b := (r.obj.left.isStrictlyLE_iff b).2 hb
  have : ((completedConstantMapComplex c hc).obj r.obj.left).IsStrictlyLE b :=
    inferInstanceAs (CochainComplex.IsStrictlyLE
      ((c.mapHomologicalComplex (.up ℤ)).obj r.obj.left) b)
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ b
  intro i
  let M := r.obj.left.X i
  have : Module.Free (AdicCompletion I A) M := (r.property.2.2.1 i).2
  have hf := SheafOfModules.flatScalarRealization_flat (ProEt.topology X) d.scalar
    M (inferInstance : Module.Flat (AdicCompletion I A) M)
  let he : (completedConstantRealization X I d.scalar).obj M ≅
      (SheafOfModules.flatScalarRealization (ProEt.topology X) d.scalar).obj M :=
    eqToIso ((completedAdicChangeData X d.scalar).choose_spec.choose _) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso d.scalar _
  have hf' : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := adicLisseCompletedRing X I)
      ((completedConstantRealization X I d.scalar).obj M) :=
    flatOnSite_of_iso X (adicLisseCompletedRing X I) he.symm hf
  exact flatOnSite_of_iso X R (e.app M).symm
    ((tr.flat_iff _).2 hf')

/-- The chain-level quotient calculation on K-flat resolutions, before replacing
an arbitrary bounded finite target by its finite-free resolution.
Source: Stacks Tags 06YN, 06YT and 06YU; the finite-free tensor computation of
Tag 093M (blueprint: lem-weil-pbc-completed-constant-resolution-tensor-calculation).


Proof: the supplied P already has the actual quotient levels and transition maps.
Form T termwise
by extending completion modules to A/I^(n+1), taking constants, and restricting
scalars. On tensors the successor transition is p tensor x mapped to its scalar
residue tensor x, which commutes with differentials and module maps.
For a bounded-above finite-free complex F, each realized term is a finite sum of H, hence
flat, and the source vanishes above its bound. It is therefore K-flat.
In each finite-free degree, tensoring its realization with a quotient is the
constant extension of that finite-free term to the quotient. The differentials
on both sides are the same matrices with scalar residues. These maps are natural
in every chain map and compatible with every quotient transition by the formula
p tensor x mapped to residue(p) tensor x. After localization they yield the
stated natural isomorphism. Restriction along the coefficient isomorphism β
is an exact monoidal equivalence, so the same calculation holds over R; conjugate
by e to replace the restricted realization by c. No conclusion for the target Q
is assumed here. -/
theorem completed_constant_resolution_tensor_calculation (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive)
    (P : CompletedConstantQuotientTower X I R β) :
    ∃ (T : CompletedConstantReductionTower X I R β h),
      (∀ r : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := R)
          ((completedConstantMapComplex c hc).obj r.obj.left)) ∧
      Nonempty
        (((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc ⋙
            completedConstantMapComplex c hc ⋙
            completedConstantTensorTower X R P.diagram) ≅
          ((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc ⋙
            T.functor ⋙ (Functor.whiskeringRight _ _ _).obj (completedConstantQ _))) := by
  let T := reductionTower X I R β h
  refine ⟨T, realized_resolution_kflat X I d R β c hc e, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft
    ((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc)
      (Functor.isoWhiskerRight (resolutionTowerIso X I d R β c hc e h P)
        ((Functor.whiskeringRight _ _ _).obj (completedConstantQ _)))

end AlgebraicGeometry.Scheme
