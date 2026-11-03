/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.PurityNormalBundle.PurityNormalBundle
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleComparisonPullbackNaturality
import all WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import all WeilConjectures.AlgebraicGeometry.Support.SupportQuotientPairPullback
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.EtaleCohomology.TateTwist.KummerClassTorsor
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.RegularIdealConormalCoordinates
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-!
# Purity conventions and the concrete rank-one datum

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-def-purity-conv/_section.md` (blueprint: sk-def-purity-conv).

The coefficient, site, twist, affine-line, normal-cone, exceptional-image,
section-invariant and deformation constructions are the imported published ones.
Here the Kummer boundary is extended to every positive annihilating exponent,
with the coefficient comparison fixed on all pure tensors. A natural-number
index r denotes the positive exponent N = r + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.PurityConventions

/-- The scalar module of the coefficient quotient over the lifted residue ring.
Source: blueprint sk-def-purity-conv, coefficient extension in the Kummer paragraph
(blueprint: sk-def-purity-conv). -/
def coefficientModule (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) :=
  letI := Module.compHom A
    ((Scheme.finiteEtaleTwistScalar m A hA).comp ULift.ringEquiv.toRingHom)
  ModuleCat.of (ULift.{u + 1} (ZMod m)) A

/-- A constant coefficient section in the published pro-etale ring sheaf.
Source: blueprint sk-def-purity-conv, pure tensors
(blueprint: sk-def-purity-conv). -/
def coefficientSection (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (W : T.ProEtᵒᵖ) (a : A) : (Scheme.tateFiniteCoefficient T A).obj.obj W :=
  ((toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app W).hom a

/-- The actual finite-twist underlying abelian sheaf, using the existing scalar extension.
Source: blueprint sk-def-purity-conv, A_T(1) = mu tensor A
(blueprint: sk-def-purity-conv). -/
def finiteLine (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) :
    Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf _).obj
    (Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA))

/-- Restriction of roots on etale objects is uniquely determined by their units.
Source: blueprint sk-def-purity-conv, root-sheaf comparison
(blueprint: sk-def-purity-conv).
Proof: restriction preserves kernels, and the restricted pro-etale units are the
same units on every etale object. The etale kernel inclusion therefore factors
uniquely through the restricted pro-etale root kernel. This factorization is
restriction of roots and commutes with power transitions. -/
theorem rootRestriction_existsUnique (T : Scheme.{u}) (m : ℕ) :
    ∃! f : T.rootsOfUnitySheaf m ⟶
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
          (Scheme.proEtaleRootsOfUnitySheaf T m),
      f ≫ (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map
          (Scheme.proEtaleRootsOfUnityInclusion T m) =
        kernel.ι (m • 𝟙 T.gmSheaf) ≫ ⟨𝟙 _⟩ := by
  let F := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  have hp : F.map (Scheme.proEtaleUnitsPower T m) =
      m • 𝟙 (F.obj (Scheme.proEtaleUnitsSheaf T)) := by
    change F.map (m • 𝟙 _) = _
    rw [F.map_nsmul]
    exact congrArg (fun f ↦ m • f) (F.map_id _)
  let e : T.gmSheaf ⟶ F.obj (Scheme.proEtaleUnitsSheaf T) := ⟨𝟙 _⟩
  have hz : m • kernel.ι (m • 𝟙 T.gmSheaf) = 0 := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using
      kernel.condition (m • 𝟙 T.gmSheaf)
  have hw : (kernel.ι (m • 𝟙 T.gmSheaf) ≫ e) ≫
      F.map (Scheme.proEtaleUnitsPower T m) = 0 := by
    rw [hp, Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, hz, zero_comp]
  let hk := isLimitOfHasKernelOfPreservesLimit F (Scheme.proEtaleUnitsPower T m)
  obtain ⟨f, hf⟩ := KernelFork.IsLimit.lift' hk
    (kernel.ι (m • 𝟙 T.gmSheaf) ≫ e) hw
  refine ⟨f, hf, fun g hg ↦ ?_⟩
  apply Fork.IsLimit.hom_ext hk
  exact hg.trans hf.symm

/-- The restriction map on roots, retained before taking its comparison-adjunction mate.
Source: blueprint sk-def-purity-conv, restriction of roots
(blueprint: sk-def-purity-conv). -/
def rootRestriction (T : Scheme.{u}) (m : ℕ) :
    T.rootsOfUnitySheaf m ⟶
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
        (Scheme.proEtaleRootsOfUnitySheaf T m) :=
  Classical.choose (rootRestriction_existsUnique T m)

/-- The normalization of coefficient comparison on every local pure tensor.
The roots comparison is the published restriction map, fixed by its inclusion in units.
Its adjoint sends an etale root to its restriction on the same pro-etale object.
Source: blueprint sk-def-purity-conv, specified coefficient identification
(blueprint: sk-def-purity-conv). -/
def IsCoefficientComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (e : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA) : Prop :=
  ∀ (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj W),
    (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _) e.hom).hom.app W
      (Scheme.kummerCoefficientInsertionApp T (l ^ (r + 1))
        (coefficientModule A (l ^ (r + 1)) hA) a W z) =
      Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
        ((Scheme.toProEt T).obj W.unop)
        (coefficientSection T A ((Scheme.toProEt T).op.obj W) a)
        ((rootRestriction T (l ^ (r + 1))).hom.app W z)

open scoped TensorProduct in
private def localTensorEquiv (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (U : T.Etaleᵒᵖ) :
    ((Scheme.kummerRootModulePresheaf T m).obj U ⊗[ULift.{u + 1} (ZMod m)]
      coefficientModule A m hA) ≃+
    ((ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA)).obj
      ((Scheme.finiteEtaleMuModulePresheaf T m).obj U)) := by
  let M := (Scheme.finiteEtaleMuModulePresheaf T m).obj U
  let a := Scheme.finiteEtaleTwistScalar m A hA
  letI : Module (ZMod m) A := Module.compHom A a
  letI : TensorProduct.CompatibleSMul (ZMod m) (ULift.{u + 1} (ZMod m)) M A :=
    ⟨fun r x y ↦ by
      change r.down • x ⊗ₜ[ZMod m] y = _
      exact TensorProduct.smul_tmul _ _ _⟩
  letI : TensorProduct.CompatibleSMul (ULift.{u + 1} (ZMod m)) (ZMod m) M A :=
    ⟨fun r x y ↦ by
      change (ULift.up r : ULift.{u + 1} (ZMod m)) • x ⊗ₜ[ULift.{u + 1} (ZMod m)] y = _
      exact TensorProduct.smul_tmul _ _ _⟩
  exact (TensorProduct.equivOfCompatibleSMul (ZMod m)
    (ULift.{u + 1} (ZMod m)) ℤ M A).toAddEquiv.trans
      (TensorProduct.comm (ZMod m) M A).toAddEquiv

private def etaleTensorPresheafIso (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) :
    ((Scheme.kummerRootModulePresheaf T m ⊗
      (Functor.const T.Etaleᵒᵖ).obj (coefficientModule A m hA)) ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}) ≅
    ((Scheme.finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA)) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents (fun U ↦ (localTensorEquiv T m A hA U).toAddCommGrpIso) (by
    intro U V f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul z a => rfl)

private def etaleTensorIso (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) :
    (Scheme.kummerAbelianTwist T m).obj (coefficientModule A m hA) ≅
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
          (Scheme.finiteEtaleTateLine T m A hA) :=
  let J := T.smallEtaleTopology
  let P := Scheme.kummerRootModulePresheaf T m ⊗
    (Functor.const T.Etaleᵒᵖ).obj (coefficientModule A m hA)
  let Q := Scheme.finiteEtaleMuModulePresheaf T m ⋙
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA)
  let F := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}
  let G := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  letI : F.IsLeftAdjoint :=
    (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} (ZMod m))).isLeftAdjoint
  letI : G.IsLeftAdjoint := (ModuleCat.forget₂CoinduceAdj A).isLeftAdjoint
  ((sheafComposeNatIso J F
    (sheafificationAdjunction J _) (sheafificationAdjunction J _)).app P).symm ≪≫
    (presheafToSheaf J AddCommGrpCat.{u + 1}).mapIso (etaleTensorPresheafIso T m A hA) ≪≫
    (sheafComposeNatIso J G
      (sheafificationAdjunction J _) (sheafificationAdjunction J _)).app Q

private theorem etaleTensorIso_generator (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (U : T.Etaleᵒᵖ)
    (a : A) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    (etaleTensorIso T m A hA).hom.hom.app U
      (Scheme.kummerCoefficientInsertionApp T m (coefficientModule A m hA) a U z) =
    Scheme.finiteEtaleTateOneGenerator A m T hA U a z := by
  let J := T.smallEtaleTopology
  let P := Scheme.kummerRootModulePresheaf T m ⊗
    (Functor.const T.Etaleᵒᵖ).obj (coefficientModule A m hA)
  let Q := Scheme.finiteEtaleMuModulePresheaf T m ⋙
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA)
  let F := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}
  let G := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let : F.IsLeftAdjoint :=
    (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} (ZMod m))).isLeftAdjoint
  let : G.IsLeftAdjoint := (ModuleCat.forget₂CoinduceAdj A).isLeftAdjoint
  have h : Functor.whiskerRight (toSheafify J P) F ≫
      (etaleTensorIso T m A hA).hom.hom =
    (etaleTensorPresheafIso T m A hA).hom ≫ Functor.whiskerRight (toSheafify J Q) G := by
    change Functor.whiskerRight (toSheafify J P) F ≫
      (sheafifyComposeIso J F P).inv ≫
      sheafifyMap J (etaleTensorPresheafIso T m A hA).hom ≫
      (sheafifyComposeIso J G Q).hom = _
    simp only [← Category.assoc]
    rw [sheafComposeIso_inv_fac, ← toSheafify_naturality]
    rw [Category.assoc, sheafComposeIso_hom_fac]
  exact congrArg (fun f ↦ f.app U (TensorProduct.tmul
    (ULift.{u + 1} (ZMod m))
    (show (Scheme.kummerRootModulePresheaf T m).obj U from z)
    (show coefficientModule A m hA from a))) h

private theorem fixedTensorPresentation_one (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) :
    ∃ e : Scheme.finiteRootProTensor A (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T ≅
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology T) A).obj
        (Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA)),
      ∀ (U : T.ProEtᵒᵖ)
        (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj U),
        e.hom.hom.app U (Scheme.finiteRootProGenerator A (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) hA T U 1 z) =
        Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA) U.unop 1 z := by
  let J := Scheme.ProEt.topology T
  let F := ConstantScalarRestriction.restriction J A
  have : F.IsEquivalence := ConstantScalarRestriction.isEquivalence J A
  let D := Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (Scheme.tateFiniteCoefficient T A)
  obtain ⟨Ψ, hcomp, hformula⟩ :=
    ProEtale.SpTowerClasses.finiteTateLine_universal T l A r
      (Scheme.finiteEtaleTwistScalar _ A hA)
  let E (N : SheafOfModules.{u + 1} R) :=
    (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans (Ψ N)
  have hE (N : SheafOfModules.{u + 1} R) (f : F.obj D ⟶ F.obj N)
      (U : T.ProEtᵒᵖ)
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj U) :
      (E N f).hom.app U z = f.hom.app U
        (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
          U.unop 1 z) := by
    have h := hformula N (F.preimage f) U 1 z
    rw [one_smul] at h
    exact h.trans (congrArg (fun g : F.obj D ⟶ F.obj N ↦
      g.hom.app U (Scheme.tateFiniteTensor T l A r
        (Scheme.finiteEtaleTwistScalar _ A hA) U.unop 1 z)) (F.map_preimage f))
  have hEc {N M : SheafOfModules.{u + 1} R}
      (f : F.obj D ⟶ F.obj N) (g : F.obj N ⟶ F.obj M) :
      E M (f ≫ g) = E N f ≫
        (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
    ext U z
    rw [hE]
    change g.hom.app U (f.hom.app U _) = g.hom.app U ((E N f).hom.app U z)
    rw [hE]
  let Q := Scheme.finiteRootProTensor A (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) hA T
  let p (N : Sheaf J (ModuleCat.{u + 1} A)) :=
    Scheme.proLineHomEquiv T (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) A hA N
  let f : Q ⟶ F.obj D := (p (F.obj D)).symm (E D (𝟙 _))
  have hfcomp (N : SheafOfModules.{u + 1} R) (g : F.obj D ⟶ F.obj N) :
      p (F.obj N) (f ≫ g) = E N g := by
    erw [Scheme.proLineHomEquiv_comp]
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    exact (hEc (𝟙 _) g).symm.trans (congrArg (E N) (Category.id_comp g))
  have hf : IsIso f := by
    apply isIso_of_coyoneda_map_bijective
    intro P
    obtain ⟨N, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage F P
    let e := (Iso.homCongr (Iso.refl _) i.symm).trans
      ((E N).trans ((p (F.obj N)).symm.trans (Iso.homCongr (Iso.refl _) i)))
    suffices (fun g ↦ f ≫ g) = e by rw [this]; exact e.bijective
    funext g
    apply (Iso.homCongr (Iso.refl _) i.symm).injective
    apply (p (F.obj N)).injective
    simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_hom,
      Iso.refl_inv, Category.id_comp, Category.assoc]
    change p (F.obj N) (f ≫ g ≫ i.inv) =
      p (F.obj N) (((p (F.obj N)).symm (E N (g ≫ i.inv)) ≫ i.hom) ≫ i.inv)
    rw [Category.assoc, i.hom_inv_id, Category.comp_id]
    exact (hfcomp N (g ≫ i.inv)).trans ((p (F.obj N)).apply_symm_apply _).symm
  refine ⟨asIso f, ?_⟩
  intro U z
  have h := congrArg (fun g ↦ g.hom.app U z) ((p (F.obj D)).apply_symm_apply (E D (𝟙 _)))
  rw [Scheme.proLineHomEquiv_generator] at h
  exact h.trans (hE D (𝟙 _) U z)

private theorem restriction_coeff_smul (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.tateFiniteCoefficient T A))) (U : T.ProEtᵒᵖ) (a : A) (x : N.val.obj U) :
    a • (show ((ConstantScalarRestriction.restriction
      (Scheme.ProEt.topology T) A).obj N).obj.obj U from x) =
    (show ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.tateFiniteCoefficient T A)).obj.obj U from coefficientSection T A U a) • x := by
  let J := Scheme.ProEt.topology T
  have hc := toSheafify_naturality J
    (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
  have hu : ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom).app U) a = coefficientSection T A U a := by
    change ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      sheafifyMap J (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of A)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom).app U) a = _
    erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  change (show ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Scheme.tateFiniteCoefficient T A)).obj.obj U from
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom).app U) a) • x = _
  exact congrArg (fun b : ((sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Scheme.tateFiniteCoefficient T A)).obj.obj U ↦ b • x) hu

private theorem fixedTensorPresentation (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) :
    ∃ e : Scheme.finiteRootProTensor A (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T ≅
      (ConstantScalarRestriction.restriction (Scheme.ProEt.topology T) A).obj
        (Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA)),
      ∀ (U : T.ProEtᵒᵖ) (a : A)
        (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj U),
        e.hom.hom.app U (Scheme.finiteRootProGenerator A (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) hA T U a z) =
        Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
          U.unop (coefficientSection T A U a) z := by
  obtain ⟨e, he⟩ := fixedTensorPresentation_one T l A r hA
  refine ⟨e, ?_⟩
  intro U a z
  rw [Scheme.proGenerator_smul, _root_.map_smul, he]
  rw [restriction_coeff_smul]
  change (show ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Scheme.tateFiniteCoefficient T A)).obj.obj U from coefficientSection T A U a) •
    (show (Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA)).val.obj U
      from Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
        U.unop 1 z) = _
  exact (SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
    (Scheme.tateFiniteScalar T l A r (Scheme.finiteEtaleTwistScalar _ A hA))
    (Scheme.purTwistRootsModule T l r) U (coefficientSection T A U a) 1 z).trans
      (congrArg (fun b ↦ Scheme.tateFiniteTensor T l A r
        (Scheme.finiteEtaleTwistScalar _ A hA) U.unop b z) (mul_one _))

private lemma rootRestriction_adjunct (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    rootRestriction T m =
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (ProEtale.cartierRootsIso T m hm hT).hom := by
  symm
  apply (rootRestriction_existsUnique T m).choose_spec.2
  rw [← Adjunction.homEquiv_naturality_right]
  exact Scheme.rootComparison_adjunct T m hm hT

private lemma kummer_tensor_hom_ext (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f g : (Scheme.kummerAbelianTwist T m).obj (coefficientModule A m hA) ⟶ F)
    (h : ∀ (U : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m).obj.obj U),
      f.hom.app U (Scheme.kummerCoefficientInsertionApp T m
        (coefficientModule A m hA) a U z) =
      g.hom.app U (Scheme.kummerCoefficientInsertionApp T m
        (coefficientModule A m hA) a U z)) : f = g := by
  let J := T.smallEtaleTopology
  let P := Scheme.kummerRootModulePresheaf T m ⊗
    (Functor.const T.Etaleᵒᵖ).obj (coefficientModule A m hA)
  let H := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}
  let : H.IsLeftAdjoint :=
    (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} (ZMod m))).isLeftAdjoint
  apply Sheaf.hom_ext
  apply (cancel_epi (sheafifyComposeIso J H P).hom).mp
  apply sheafify_hom_ext J _ _ F.property
  simp only [← Category.assoc, sheafComposeIso_hom_fac]
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z a => exact h U a z

/-- There is exactly one coefficient comparison with the specified local tensor formula.
Source: blueprint sk-def-purity-conv, comparison paragraph
(blueprint: sk-def-purity-conv).
Proof: change the lifted residue-ring tensor into the ordinary scalar-extension tensor,
then commute coefficient forgetting with sheafification by its coinduction adjunction.
The finite-line universal property and constant scalar restriction identify the pro-etale
tensor presentation with the given finite line. Compose these presentations with the
normalized finite-root site comparison. The generator formulas give the prescribed
adjunct. The sheafification universal property and pure-tensor induction give uniqueness.
No freeness of A over Z/l^N or divisibility of n by the ramification index is used. -/
theorem coefficientComparison_existsUnique (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    ∃! e : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA,
      IsCoefficientComparison T l A r hA e := by
  let hm := pow_pos (Fact.out : l.Prime).pos (r + 1)
  obtain ⟨eP, heP⟩ := fixedTensorPresentation T l A r hA
  have hσ := Scheme.sigmaMap_isIso A (l ^ (r + 1)) hm hA T hT
  let ν := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T
  let H := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let eE := etaleTensorIso T (l ^ (r + 1)) A hA
  let eF := (ProEtale.forgetComparisonIso A T).app
    (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) A hA)
  let σ := Scheme.sigmaMap A (l ^ (r + 1)) hm hA T hT
  let e : ν.obj ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
      (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA :=
    ν.mapIso eE ≪≫ eF ≪≫ H.mapIso (asIso σ) ≪≫ H.mapIso eP
  have he : IsCoefficientComparison T l A r hA e := by
    intro U a z
    change (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _)
      (ν.map eE.hom ≫ eF.hom ≫ H.map σ ≫ H.map eP.hom)).hom.app U
        (Scheme.kummerCoefficientInsertionApp T (l ^ (r + 1))
          (coefficientModule A (l ^ (r + 1)) hA) a U z) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hF := ProEtale.forgetComparisonIso_hom A T
      (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) A hA)
    change eF.hom = _ at hF
    rw [hF, Equiv.apply_symm_apply]
    change eP.hom.hom.app ((Scheme.toProEt T).op.obj U)
      (σ.hom.app ((Scheme.toProEt T).op.obj U)
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) A hA)).hom.app U
            (eE.hom.hom.app U (Scheme.kummerCoefficientInsertionApp T (l ^ (r + 1))
              (coefficientModule A (l ^ (r + 1)) hA) a U z)))) = _
    rw [etaleTensorIso_generator]
    change eP.hom.hom.app ((Scheme.toProEt T).op.obj U)
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _ σ).hom.app U
        (Scheme.finiteEtaleTateOneGenerator A (l ^ (r + 1)) T hA U a z)) = _
    rw [Scheme.sigmaMap_adjunct_generator]
    erw [heP]
    rw [← rootRestriction_adjunct T (l ^ (r + 1)) hm hT]
    rfl
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _).injective
  apply kummer_tensor_hom_ext T (l ^ (r + 1)) A hA
  intro U a z
  exact (hd U a z).trans (he U a z).symm

/-- The unique comparison, with its root and pure-tensor normalization retained.
Source: blueprint sk-def-purity-conv, coefficient identification
(blueprint: sk-def-purity-conv). -/
def coefficientComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA :=
  Classical.choose (coefficientComparison_existsUnique T l A r hA hT)

/-- The actual Kummer boundary, coefficient insertion and canonical site comparison.
This formula gives kappa(v) for every unit, and hence kappa(t) for the coordinate.
Source: blueprint sk-def-purity-conv, displayed definition of kappa(t)
(blueprint: sk-def-purity-conv). -/
def kummer (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (v : Γ(T, ⊤)ˣ) : Sheaf.H (finiteLine T l A r hA) 1 :=
  Sheaf.H.map (coefficientComparison T l A r hA hT).hom 1
    (ProEtale.comparisonCohomologyMap T _ 1
      (Sheaf.H.map
        (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
          (coefficientModule A (l ^ (r + 1)) hA) (1 : A)) 1
        (T.kummerδ₀ (l ^ (r + 1)) hT (Additive.ofMul v))))

private def coefficientRootMap (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
      (T.rootsOfUnitySheaf (l ^ (r + 1))) ⟶ finiteLine T l A r hA :=
  (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map
    (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
      (coefficientModule A (l ^ (r + 1)) hA) (1 : A)) ≫
    (coefficientComparison T l A r hA hT).hom

private lemma coefficientRootMap_normalization (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj W) :
    (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _)
      (coefficientRootMap T l A r hA hT)).hom.app W z =
    Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
      ((Scheme.toProEt T).obj W.unop)
      (coefficientSection T A ((Scheme.toProEt T).op.obj W) 1)
      ((rootRestriction T (l ^ (r + 1))).hom.app W z) := by
  unfold coefficientRootMap
  rw [Adjunction.homEquiv_naturality_left]
  exact (coefficientComparison_existsUnique T l A r hA hT).choose_spec.1 W 1 z

private theorem finiteLine_hom_ext (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    {F : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (f g : finiteLine T l A n hA ⟶ F)
    (h : ∀ (V : T.ProEt) (b : (Scheme.tateFiniteCoefficient T A).obj.obj (op V))
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op V)),
      f.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hA) V b z) =
        g.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hA) V b z)) :
    f = g := by
  let α := Scheme.tateFiniteScalar T l A n (Scheme.finiteEtaleTwistScalar _ A hA)
  let M := Scheme.purTwistRootsModule T l n
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M
  apply ((sheafificationAdjunction (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}).homEquiv P.presheaf F).injective
  ext U x
  change f.hom.app U ((toSheafify (Scheme.ProEt.topology T) P.presheaf).app U x) =
    g.hom.app U ((toSheafify (Scheme.ProEt.topology T) P.presheaf).app U x)
  let := (α.hom.app U).hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b z => exact h U.unop b z

private theorem finiteLine_tensor_restrict (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) {U V : T.ProEtᵒᵖ} (i : U ⟶ V)
    (b : (Scheme.tateFiniteCoefficient T A).obj.obj U)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj U) :
    (finiteLine T l A r hA).obj.map i
        (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
          U.unop b z) =
      Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
        V.unop ((Scheme.tateFiniteCoefficient T A).obj.map i b)
        ((Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.map i z) := by
  let α := Scheme.tateFiniteScalar T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
  let M := Scheme.purTwistRootsModule T l r
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M
  let z' : M.val.obj U := z
  have h := NatTrans.naturality_apply
    (toSheafify (Scheme.ProEt.topology T) P.presheaf) i
      (b ⊗ₜ[(Scheme.purTwistFiniteRing T l r).obj.obj U, (α.hom.app U).hom] z')
  have hm := SheafOfModules.changeOfRingsMap_tmulOfUniverses α M i b z'
  exact h.symm.trans (congrArg (fun t ↦
    (toSheafify (Scheme.ProEt.topology T) P.presheaf).app V t) hm)

private theorem finiteLine_const_hom_ext (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    {F : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (f g : finiteLine T l A r hA ⟶ F)
    (h : ∀ (V : T.ProEt) (a : A)
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op V)),
      f.hom.app (op V)
          (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
            V (coefficientSection T A (op V) a) z) =
        g.hom.app (op V)
          (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
            V (coefficientSection T A (op V) a) z)) : f = g := by
  apply finiteLine_hom_ext T l A r hA f g
  intro V b z
  let η := toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))
  apply F.property.isSeparated _ _
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology T) η b)
  intro W i hi
  obtain ⟨a, ha⟩ := hi
  have hf := NatTrans.naturality_apply f.hom i.op
    (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA) V b z)
  have hg := NatTrans.naturality_apply g.hom i.op
    (Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA) V b z)
  rw [finiteLine_tensor_restrict] at hf hg
  change coefficientSection T A (op W) a =
    (Scheme.tateFiniteCoefficient T A).obj.map i.op b at ha
  rw [← ha] at hf hg
  exact hf.symm.trans ((h W a _).trans hg)

/-- The finite line pullback is characterized by restriction of roots and constants.
Source: blueprint sk-def-purity-conv, naturality paragraph
(blueprint: sk-def-purity-conv).
Proof: pullback of roots is the canonical root-restriction isomorphism; pullback of
constant A is the constant-sheaf isomorphism. The universal property of the sheafified
tensor gives this map. After an etale root trivialization it is the identity on A,
so it is an isomorphism. Local sums of pure tensors prove uniqueness. -/
theorem finiteLinePullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) :
    ∃! e : (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
        (finiteLine Y l A r hA) ≅ finiteLine X l A r hA,
      ∀ (V : Y.ProEt) (a : A)
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (r + 1))).obj.obj (op V)),
        (((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
          e.hom).hom.app (op V)
            (Scheme.tateFiniteTensor Y l A r (Scheme.finiteEtaleTwistScalar _ A hA)
              V (coefficientSection Y A (op V) a) z) =
          Scheme.tateFiniteTensor X l A r (Scheme.finiteEtaleTwistScalar _ A hA)
            ((Scheme.proEtaleBaseChange f).obj V)
            (coefficientSection X A (op ((Scheme.proEtaleBaseChange f).obj V)) a)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (r + 1))).hom.app
              (op V) z) := by
  have hlY : IsUnit (l : Γ(Y, ⊤)) :=
    (isUnit_pow_iff (Nat.succ_ne_zero r)).mp (by
      simpa only [Nat.cast_pow] using hY)
  have hlX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hlY.map f.appTop.hom
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (show IsUnit (l : Y.residueField y) from by
      simpa only [map_natCast] using hlY.map (Y.Γevaluation y).hom).invertible
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using hlX.map (X.Γevaluation x).hom).invertible
  let R := Scheme.tateFiniteCoefficient Y A
  let S := Scheme.tateFiniteCoefficient X A
  let c := ProEtale.StrictTower.constantRingIso A f
  let M := Scheme.tateFiniteLine Y l A r (Scheme.finiteEtaleTwistScalar _ A hA)
  let UY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let UX := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  let adj := ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let unit := UY.map ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M)
  let k₀ := (adj.homEquiv (UY.obj M)
    (UX.obj ((Scheme.proEtaleRingModulePullback f R S c).obj M))).symm unit
  have hk₀ : IsIso k₀ := ProEtale.pullback_unit_mate_isIso f R S c M
  let k := ProEtale.finiteFirstComparison f l A r (Scheme.finiteEtaleTwistScalar _ A hA)
  have hk : IsIso k :=
    ProEtale.finiteFirstComparison_isIso f l A r (Scheme.finiteEtaleTwistScalar _ A hA)
  let e : (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
      (finiteLine Y l A r hA) ≅ finiteLine X l A r hA :=
    asIso (k₀ ≫ UX.map k)
  have he (V : Y.ProEt) (a : A)
      (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (r + 1))).obj.obj (op V)) :
      ((adj.homEquiv _ _) e.hom).hom.app (op V)
          (Scheme.tateFiniteTensor Y l A r (Scheme.finiteEtaleTwistScalar _ A hA)
            V (coefficientSection Y A (op V) a) z) =
        Scheme.tateFiniteTensor X l A r (Scheme.finiteEtaleTwistScalar _ A hA)
          ((Scheme.proEtaleBaseChange f).obj V)
          (coefficientSection X A (op ((Scheme.proEtaleBaseChange f).obj V)) a)
          ((Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (r + 1))).hom.app
            (op V) z) := by
    have hm := ProEtale.finiteFirstComparison_apply f l A r
      (Scheme.finiteEtaleTwistScalar _ A hA) V (coefficientSection Y A (op V) a) z
    have hc := ((sheafificationAdjunction (Scheme.ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S)).apply_symm_apply
          (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
            (toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
    have hca := congrArg (fun q ↦ (q.app (op V)).hom a) hc
    change (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A)).hom.app (op V) (coefficientSection Y A (op V) a) =
      coefficientSection X A (op ((Scheme.proEtaleBaseChange f).obj V)) a at hca
    rw [hca] at hm
    change ((adj.homEquiv _ _) (k₀ ≫ UX.map k)).hom.app (op V) _ = _
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact hm
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply (adj.homEquiv _ _).injective
  apply finiteLine_const_hom_ext Y l A r hA
  intro V a z
  exact (hd V a z).trans (he V a z).symm

/-- The unique root-normalized pullback isomorphism.
Source: blueprint sk-def-purity-conv, pullback convention
(blueprint: sk-def-purity-conv). -/
def finiteLinePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
      (finiteLine Y l A r hA) ≅ finiteLine X l A r hA :=
  Classical.choose (finiteLinePullback_existsUnique f l A r hA hY)

private lemma etaleRootsPullback_eq (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) :
    ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r f hY).hom =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f := by
  apply (cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf))).mp
  rw [Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
  exact ((Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.1 f hY).symm

private lemma coefficientRootMap_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (hX : IsUnit ((l ^ (r + 1) : ℕ) : Γ(X, ⊤))) :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map
        (coefficientRootMap Y l A r hA hY) ≫ (finiteLinePullback f l A r hA hY).hom =
      (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app
          (Y.rootsOfUnitySheaf (l ^ (r + 1))) ≫
        (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf (l ^ (r + 1)) f) ≫
        coefficientRootMap X l A r hA hX := by
  have hm := pow_pos (Fact.out : l.Prime).pos (r + 1)
  rw [← etaleRootsPullback_eq A (l ^ (r + 1)) hm hA f hY]
  apply (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} Y).comp
    (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1})).homEquiv _ _).injective
  rw [Scheme.transpose_comparison_ab]
  rw [Scheme.composite_transpose, Scheme.composite_transpose]
  -- Name the four adjunctions: the generic pattern made `erw` try (and fail, slowly) to unify
  -- with every other `homEquiv` occurrence at default transparency.
  erw [(Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv_naturality_left,
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv_naturality_left,
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} Y).homEquiv_naturality_right,
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_naturality_right]
  ext U z
  change (((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
      (finiteLinePullback f l A r hA hY).hom).hom.app ((Scheme.toProEt Y).op.obj U))
        ((((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} Y).homEquiv _ _)
          (coefficientRootMap Y l A r hA hY)).hom.app U z) = _
  rw [coefficientRootMap_normalization]
  dsimp only [finiteLinePullback]
  erw [(finiteLinePullback_existsUnique f l A r hA hY).choose_spec.1]
  change _ = ((ProEtale.lowerStarCompComparisonLowerStarIso f
      AddCommGrpCat.{u + 1}).inv.app (finiteLine X l A r hA)).hom.app U
    ((((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
      (((Scheme.finiteEtaleTwistPullbackData A (l ^ (r + 1)) hm hA).r f hY).hom ≫
        ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv _ _)
          (coefficientRootMap X l A r hA hX))).hom.app U z)
  rw [Scheme.rightComparison_component]
  erw [Adjunction.homEquiv_naturality_right]
  change _ = (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv _ _)
      (coefficientRootMap X l A r hA hX)).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
        ((((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
          ((Scheme.finiteEtaleTwistPullbackData A (l ^ (r + 1)) hm hA).r f hY).hom).hom.app U z)
  rw [coefficientRootMap_normalization,
    rootRestriction_adjunct Y (l ^ (r + 1)) hm hY,
    rootRestriction_adjunct X (l ^ (r + 1)) hm hX,
    Scheme.rootComparison_adjunct_square A (l ^ (r + 1)) hm hA f hY hX]
  try rfl

set_option maxHeartbeats 2000000 in
-- Comparing composite adjunctions unfolds the site and module presentations.
set_option maxHeartbeats 2000000 in
-- Normalize the cohomology pullback maps through their site adjunctions.
/-- The affine-local pure-codimension convention, including the empty sequence at c=0.
Only neighbourhoods of points of Z are required, so a codimension-zero clopen component
is allowed. Source: blueprint sk-def-purity-conv, normal-cone paragraph
(blueprint: sk-def-purity-conv). -/
def IsRegularOfPureCodimension {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) : Prop :=
  ∀ z : Z, ∃ U : X.affineOpens, i z ∈ U.1 ∧
    ∃ f : List Γ(X, U.1), f.length = c ∧
      RingTheory.Sequence.IsRegular Γ(X, U.1) f ∧ Ideal.ofList f = i.ker.ideal U

/-- The canonical conormal comparison is an isomorphism and the conormal has rank c.
The normal cone is the recorded relative spectrum, with its recorded augmentation
zero section; this identifies it with the symmetric-algebra rank-c normal bundle.
Source: blueprint sk-def-purity-conv, normal-cone paragraph; Stacks Tags 0637 and 00LN
(blueprint: sk-def-purity-conv).
Proof: on each affine neighbourhood in the definition, the regular generators give
a basis of I/I^2 of length c. Lem-pur-regular-sequence-graded-polynomial identifies
the associated graded algebra with the polynomial algebra on this basis, and its
map is precisely the canonical symmetric comparison of lem-pur-conormal-graded-algebra.
These local isomorphisms and bases descend. The relative spectrum is contravariant,
so this identifies its cone with the vector bundle. The comparison preserves degree
zero and the positive-degree augmentation ideal, so also identifies the zero sections.
For c=0 use the empty regular sequence: the ideal is zero near Z, the conormal is
zero, and both graded algebras are O_Z in degree zero. -/
theorem regularNormalBundle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) (h : IsRegularOfPureCodimension i c) :
    (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison i) := by
  classical
  have hchart (z : Z) : ∃ (U : X.affineOpens) (x : Fin c → Γ(X, U.1)),
      i z ∈ U.1 ∧ Ideal.span (Set.range x) = i.ker.ideal U ∧
        RingTheory.Sequence.IsRegular Γ(X, U.1) (List.ofFn x) := by
    obtain ⟨U, hz, f, hlen, hreg, hI⟩ := h z
    subst c
    refine ⟨U, f.get, hz, ?_, ?_⟩
    · have hset : Set.range f.get = {r | r ∈ f} := by
        ext r
        simp
      simpa only [hset, Ideal.ofList] using hI
    · simpa only [List.ofFn_get] using hreg
  choose U x hz hI hr using hchart
  choose a b ha hb hm hf hbij using fun z : Z ↦
    ConormalGradedAlgebra.regular_ideal_conormal_coordinates i (U z) c (x z) (hI z) (hr z)
  have hcover : ⨆ z : Z, i ⁻¹ᵁ (U z).1 = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
  constructor
  · apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free _
      (fun z : Z ↦ (i ⁻¹ᵁ (U z).1).ι)
    · simpa only [Scheme.Opens.opensRange_ι] using hcover
    · intro z
      exact ⟨Scheme.Modules.overIsoFreeEquiv _ _ _ (hf z).some⟩
  · let f := ConormalGradedAlgebra.symmetricComparison i
    have hpiece := (ConormalGradedAlgebra.presentation i).pieceQuasicoherent 1
    have hsrc := (quasiCoherentSymmetricAlgebra_affine_comparison Z
      (ConormalGradedAlgebra.piece i 1)).1
    have hdst := (ConormalGradedAlgebra.presentation i).quasicoherent
    have hsrc' : ((commAlgebraSheafModuleFunctor Z.sheaf).obj
        (SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece i 1))).IsQuasicoherent :=
      hsrc
    have hdst' : ((commAlgebraSheafModuleFunctor Z.sheaf).obj
        (ConormalGradedAlgebra.presentation i).algebra).IsQuasicoherent := hdst
    have hmodule : IsIso ((commAlgebraSheafModuleFunctor Z.sheaf).map f) := by
      apply Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover _
        (fun z : Z ↦ i ⁻¹ᵁ (U z).1) hcover (fun z ↦ (U z).2.preimage i)
      intro z
      exact hbij z
    have hval : IsIso ((commAlgebraSheafModuleFunctor Z.sheaf).map f).val := by
      -- Elaborate the functor image first, so that `_` is solved before the defeq check.
      have h := Functor.map_isIso (SheafOfModules.forget _)
        ((commAlgebraSheafModuleFunctor Z.sheaf).map f)
      exact h
    have happ (W : Z.Opensᵒᵖ) : IsIso (f.right.hom.app W) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      have : IsIso (((commAlgebraSheafModuleFunctor Z.sheaf).map f).val.app W) := by
        have h := Functor.map_isIso (PresheafOfModules.evaluation _ W)
          ((commAlgebraSheafModuleFunctor Z.sheaf).map f).val
        exact h
      exact ConcreteCategory.bijective_of_isIso
        (((commAlgebraSheafModuleFunctor Z.sheaf).map f).val.app W)
    have : IsIso f.right.hom := NatIso.isIso_of_isIso_app _
    have : IsIso f.right := by
      refine ⟨⟨ObjectProperty.homMk (inv f.right.hom), ?_, ?_⟩⟩
      · apply Sheaf.hom_ext
        exact IsIso.hom_inv_id f.right.hom
      · apply Sheaf.hom_ext
        exact IsIso.inv_hom_id f.right.hom
    have : IsIso ((Under.forget _).map f) := ‹IsIso f.right›
    exact isIso_of_reflects_iso f (Under.forget _)

end WeilConjectures.PurityConventions
