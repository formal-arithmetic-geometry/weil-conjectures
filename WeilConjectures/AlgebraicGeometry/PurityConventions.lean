/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.PurityNormalBundle
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.FixedFinitePositiveCoefficientTwist
import all WeilConjectures.AlgebraicGeometry.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.FiniteTateLineUniversal
import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleComparisonPullbackNaturality
import all WeilConjectures.AlgebraicGeometry.SupportSiteComparison
import all WeilConjectures.AlgebraicGeometry.SupportQuotientPairPullback
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.EtaleCohomology.TateTwist.KummerClassTorsor
import WeilConjectures.AlgebraicGeometry.RegularIdealConormalCoordinates
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import all WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement

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

/-- The canonical pullback identification of constant abelian sheaves.
Source: blueprint sk-def-purity-conv, pullback convention
(blueprint: sk-def-purity-conv). -/
def constantPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
      ProEtale.upperStar AddCommGrpCat.{u + 1} f ≅
        constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft
    (constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.proEtaleBaseChange f)
      AddCommGrpCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm ≪≫
    (Scheme.proEtaleBaseChange f).constantSheafsheafPullbackIso AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (terminalIsTerminal : IsTerminal (⊤_ Y.ProEt))
      (terminalIsTerminal.isTerminalObj (Scheme.proEtaleBaseChange f))

private lemma constantPullbackIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantPullbackIso f =
      ProEtale.constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [ProEtale.CachedConstantCoherence.proConstant_eq_inverse]
  let J := Scheme.ProEt.topology Y
  let K := Scheme.ProEt.topology X
  let G := Scheme.proEtaleBaseChange f
  let a := ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let b := G.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} J K
  apply (a.homEquiv _ _).injective
  unfold Scheme.constantInverse
  erw [Equiv.apply_symm_apply]
  change a.homEquiv _ _
    (((b.leftAdjointUniq a).inv.app ((constantSheaf J AddCommGrpCat.{u + 1}).obj M)) ≫
      (G.constantSheafsheafPullbackIso AddCommGrpCat.{u + 1} J K
        (terminalIsTerminal : IsTerminal (⊤_ Y.ProEt))
        (terminalIsTerminal.isTerminalObj G)).hom.app M) = _
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit]
  let ay := constantSheafAdj J AddCommGrpCat.{u + 1}
    (terminalIsTerminal : IsTerminal (⊤_ Y.ProEt))
  let ax := constantSheafAdj K AddCommGrpCat.{u + 1}
    (terminalIsTerminal.isTerminalObj G : IsTerminal (G.obj (⊤_ Y.ProEt)))
  let d := G.sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u + 1} J K (op (⊤_ Y.ProEt))
  let ac := (ay.comp b).ofNatIsoRight d
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  apply (ay.homEquiv _ _).injective
  apply (cancel_mono (d.hom.app ((constantSheaf K AddCommGrpCat.{u + 1}).obj M))).mp
  change ac.homEquiv _ _ ((ac.leftAdjointUniq ax).hom.app M) = _
  rw [h]
  simp only [ay, ax, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app,
    Category.id_comp]
  change _ = (toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj M)).app (op (⊤_ Y.ProEt)) ≫
    (Scheme.constantDirect J K G M).hom.app (op (⊤_ Y.ProEt))
  exact (Scheme.constantDirect_unit J K G M (op (⊤_ Y.ProEt))).symm

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

/-- Cohomology pullback uses exact inverse image and the constant-integer identification.
Source: blueprint sk-def-purity-conv, base-change compatibility
(blueprint: sk-def-purity-conv). -/
def finiteLineCohomologyPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) (q : ℕ) :
    Sheaf.H (finiteLine Y l A r hA) q →+ Sheaf.H (finiteLine X l A r hA) q :=
  (Sheaf.H.map (finiteLinePullback f l A r hA hY).hom q).comp
    (Sheaf.H.mapFunctor (ProEtale.upperStar AddCommGrpCat.{u + 1} f)
      ((constantPullbackIso f).symm.app (AddCommGrpCat.of (ULift ℤ)))
      (finiteLine Y l A r hA) q)

private lemma etaleRootsPullback_eq (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) :
    ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r f hY).hom =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f := by
  apply (cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf))).mp
  rw [Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
  exact ((Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.1 f hY).symm

set_option maxHeartbeats 2000000 in
-- Comparing composite adjunctions unfolds the site and module presentations.
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
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
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
-- Normalize the cohomology pullback maps through their site adjunctions.
/-- The constructed class commutes with arbitrary scheme pullback.
Source: blueprint sk-def-purity-conv, naturality paragraph
(blueprint: sk-def-purity-conv).
Proof: pullback of the Kummer exact sequence is the Kummer sequence; its connecting
map is natural. Coefficient insertion commutes with restriction on every root.
Comparison inverse images commute with base change by the site functor square.
Both resulting coefficient identifications have the pure-tensor normalization,
so uniqueness identifies them. Compose these three commuting squares. -/
theorem kummer_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (hX : IsUnit ((l ^ (r + 1) : ℕ) : Γ(X, ⊤))) (v : Γ(Y, ⊤)ˣ) :
    finiteLineCohomologyPullback f l A r hA hY 1 (kummer Y l A r hA hY v) =
      kummer X l A r hA hX (Units.map f.appTop.hom v) := by
  have hconst := constantPullbackIso_eq f
  have hs : (ProEtale.supportSiteComparisonCoefficientPullbackIso
        AddCommGrpCat.{u + 1} f).hom.app (Y.rootsOfUnitySheaf (l ^ (r + 1))) ≫
      (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map
        (coefficientRootMap Y l A r hA hY) ≫ (finiteLinePullback f l A r hA hY).hom =
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf (l ^ (r + 1)) f) ≫
      coefficientRootMap X l A r hA hX := by
    rw [coefficientRootMap_baseChange f l A r hA hY hX]
    change (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).hom.app _ ≫
      (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app _ ≫ _ = _
    rw [Iso.hom_inv_id_app_assoc]
  let δ := Y.kummerδ₀ (l ^ (r + 1)) hY (Additive.ofMul v)
  let x := ProEtale.comparisonCohomologyMap X _ 1
    (Etale.cohomologyMap f (Y.rootsOfUnitySheaf (l ^ (r + 1))) 1 δ)
  have hcomp := congrArg (fun g ↦ g δ)
    (ProEtale.comparisonCohomologyMap_pullback f (Y.rootsOfUnitySheaf (l ^ (r + 1))) 1)
  calc
    _ = Sheaf.H.map ((ProEtale.upperStar AddCommGrpCat.{u + 1} f).map
          (coefficientRootMap Y l A r hA hY) ≫
        (finiteLinePullback f l A r hA hY).hom) 1
      (ProEtale.cohomologyMap f _ 1 (ProEtale.comparisonCohomologyMap Y _ 1 δ)) := by
      simp only [finiteLineCohomologyPullback, AddMonoidHom.comp_apply, hconst,
        ProEtale.cohomologyMap, kummer, coefficientRootMap, ProEtale.comparisonCohomologyMap,
        Sheaf.H.mapFunctor_map, Sheaf.H.map_comp_apply, Functor.map_comp, δ]
    _ = Sheaf.H.map
      ((ProEtale.supportSiteComparisonCoefficientPullbackIso
          AddCommGrpCat.{u + 1} f).hom.app (Y.rootsOfUnitySheaf (l ^ (r + 1))) ≫
        (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map
          (coefficientRootMap Y l A r hA hY) ≫
        (finiteLinePullback f l A r hA hY).hom) 1 x := by
      conv_rhs => rw [Sheaf.H.map_comp_apply]
      exact congrArg (Sheaf.H.map _ 1) hcomp
    _ = Sheaf.H.map ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map
        (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf (l ^ (r + 1)) f) ≫
      coefficientRootMap X l A r hA hX) 1 x := by
      rw [hs]
      rfl
    _ = _ := by
      rw [Sheaf.H.map_comp_apply]
      dsimp [x, δ]
      rw [ProEtale.comparisonCohomologyMap, ← Sheaf.H.mapFunctor_map,
        Scheme.sheafH_map_cohomologyMap_kummerδ₀ f (l ^ (r + 1)) hY hX v]
      simp only [coefficientRootMap, kummer, Sheaf.H.map_comp_apply,
        ProEtale.comparisonCohomologyMap, Sheaf.H.mapFunctor_map]

/-- The canonical exponent comparison is the existing finite Kummer identification,
expressed with the unique quotient scalar maps and fixed on every pure tensor.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv).
Proof: the two unital quotient maps to A agree by the universal property of ZMod.
Transport spFiniteKummer along that equality. Its specified power formula gives
the displayed formula, including r=n. Pure tensors locally generate the scalar
extension, so this formula determines the isomorphism uniquely. -/
theorem finiteLineTransition_existsUnique (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    ∃! e : finiteLine T l A n hn ≅ finiteLine T l A r hr,
      ∀ (V : T.ProEt) (b : (Scheme.tateFiniteCoefficient T A).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op V)),
        e.hom.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hn) V b z) =
          Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hr) V b
            ((Scheme.proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.succ_le_succ hrn))).hom.app (op V) z) := by
  have hl : IsUnit (l : Γ(T, ⊤)) :=
    (isUnit_pow_iff (Nat.succ_ne_zero r)).mp (by
      simpa only [Nat.cast_pow] using hT)
  let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      simpa only [map_natCast] using hl.map (T.Γevaluation x).hom).invertible
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hf⟩ := Scheme.tateTwist_finite_locallyFree T l
  obtain ⟨a, ha, _⟩ := hf A r (fun b ↦ by
    rw [nsmul_eq_mul, hr, zero_mul])
  have har : a = Scheme.finiteEtaleTwistScalar _ A hr := Subsingleton.elim _ _
  subst a
  have han : (Scheme.finiteEtaleTwistScalar _ A hr).comp
      (ZMod.castHom (pow_dvd_pow l (Nat.succ_le_succ hrn))
        (ZMod (l ^ (r + 1)))) = Scheme.finiteEtaleTwistScalar _ A hn :=
    Subsingleton.elim _ _
  have hmap := ha n hrn
  rw [han] at hmap
  obtain ⟨k, hk, hformula⟩ := hmap
  let := hk
  let e := (SheafOfModules.toSheaf _).mapIso (asIso k)
  refine ⟨e, hformula, ?_⟩
  intro d hd
  apply Iso.ext
  apply finiteLine_hom_ext T l A n hn
  intro V b z
  exact (hd V b z).trans (hformula V b z).symm

/-- The unique canonical power-transition identification at admissible exponents.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv). -/
def finiteLineTransition (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    finiteLine T l A n hn ≅ finiteLine T l A r hr :=
  Classical.choose (finiteLineTransition_existsUnique T l A r n hrn hr hn hT)

private lemma boundary_power (T : Scheme.{u}) (m n : ℕ) (hmn : m ∣ n)
    (hm : IsUnit (m : Γ(T, ⊤))) (hn : IsUnit (n : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf n ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (n / m) • kernel.ι (n • 𝟙 T.gmSheaf))
    (v : Γ(T, ⊤)ˣ) :
    Sheaf.H.map q 1 (T.kummerδ₀ n hn (Additive.ofMul v)) =
      T.kummerδ₀ m hm (Additive.ofMul v) := by
  let φ : T.kummerSequence n ⟶ T.kummerSequence m :=
    { τ₁ := q
      τ₂ := (n / m) • 𝟙 T.gmSheaf
      τ₃ := 𝟙 T.gmSheaf
      comm₁₂ := by
        change q ≫ kernel.ι (m • 𝟙 T.gmSheaf) =
          kernel.ι (n • 𝟙 T.gmSheaf) ≫ ((n / m) • 𝟙 T.gmSheaf)
        simpa only [Preadditive.comp_nsmul, Category.comp_id] using hq
      comm₂₃ := by
        dsimp [Scheme.kummerSequence]
        simp only [Preadditive.comp_nsmul,
          Category.comp_id, smul_smul, Nat.mul_div_cancel' hmn] }
  rw [Scheme.kummerδ₀_eq_δSucc, Scheme.kummerδ₀_eq_δSucc]
  have h := Sheaf.H.map_δSucc (T.kummerSequence_shortExact n hn)
    (T.kummerSequence_shortExact m hm) φ 0
    ((Sheaf.H.equiv₀ T.gmSheaf terminalIsTerminal).symm (Scheme.gmSection v))
  change Sheaf.H.map q 1
      (Sheaf.H.δSucc (T.kummerSequence_shortExact n hn) 0 _) =
    Sheaf.H.δSucc (T.kummerSequence_shortExact m hm) 0
      (Sheaf.H.map (𝟙 T.gmSheaf) 0 _) at h
  rw [Sheaf.H.map_id_apply] at h
  exact h

private lemma roots_power_exists (T : Scheme.{u}) (m n : ℕ) (hmn : m ∣ n) :
    ∃ q : T.rootsOfUnitySheaf n ⟶ T.rootsOfUnitySheaf m,
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (n / m) • kernel.ι (n • 𝟙 T.gmSheaf) := by
  have h : ((n / m) • kernel.ι (n • 𝟙 T.gmSheaf)) ≫ (m • 𝟙 T.gmSheaf) = 0 := by
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.comp_id, smul_smul, Nat.mul_div_cancel' hmn] using
      kernel.condition (n • 𝟙 T.gmSheaf)
  exact ⟨kernel.lift _ _ h, kernel.lift_ι _ _ h⟩

private lemma restriction_power (T : Scheme.{u}) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (q : T.rootsOfUnitySheaf n ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (n / m) • kernel.ι (n • 𝟙 T.gmSheaf)) :
    q ≫ rootRestriction T m = rootRestriction T n ≫
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map
        (Scheme.proEtaleRootsOfUnityTransition T m n hm hn hmn) := by
  let F := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  have hi (k : ℕ) : Mono (Scheme.proEtaleRootsOfUnityInclusion T k) := by
    unfold Scheme.proEtaleRootsOfUnityInclusion
    infer_instance
  have := hi m
  have ht : Scheme.proEtaleRootsOfUnityTransition T m n hm hn hmn ≫
      Scheme.proEtaleRootsOfUnityInclusion T m =
        (n / m) • Scheme.proEtaleRootsOfUnityInclusion T n := by
    unfold Scheme.proEtaleRootsOfUnityTransition Scheme.proEtaleRootsOfUnityInclusion
    rw [kernel.lift_ι]
    simp only [Preadditive.comp_nsmul, Category.comp_id]
  have hr (k : ℕ) : rootRestriction T k ≫
      F.map (Scheme.proEtaleRootsOfUnityInclusion T k) =
      kernel.ι (k • 𝟙 T.gmSheaf) ≫ (⟨𝟙 _⟩ : T.gmSheaf ⟶
        F.obj (Scheme.proEtaleUnitsSheaf T)) :=
    (rootRestriction_existsUnique T k).choose_spec.1
  change q ≫ rootRestriction T m = rootRestriction T n ≫ F.map _
  apply (cancel_mono (F.map (Scheme.proEtaleRootsOfUnityInclusion T m))).mp
  simp only [Category.assoc, ← F.map_comp, ht, F.map_nsmul,
    Preadditive.comp_nsmul, hr]
  rw [← Category.assoc, hq, Preadditive.nsmul_comp]

private lemma coefficientRootMap_power (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hTr : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hTn : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf (l ^ (n + 1)) ⟶ T.rootsOfUnitySheaf (l ^ (r + 1)))
    (hq : q ≫ kernel.ι ((l ^ (r + 1)) • 𝟙 T.gmSheaf) =
      ((l ^ (n + 1)) / (l ^ (r + 1))) •
        kernel.ι ((l ^ (n + 1)) • 𝟙 T.gmSheaf)) :
    coefficientRootMap T l A n hn hTn ≫
      (finiteLineTransition T l A r n hrn hr hn hTr).hom =
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map q ≫
      coefficientRootMap T l A r hr hTr := by
  let adj := ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  ext W z
  change (finiteLineTransition T l A r n hrn hr hn hTr).hom.hom.app
    ((Scheme.toProEt T).op.obj W)
      (((adj.homEquiv _ _) (coefficientRootMap T l A n hn hTn)).hom.app W z) =
    (((adj.homEquiv _ _) (coefficientRootMap T l A r hr hTr)).hom.app W (q.hom.app W z))
  rw [coefficientRootMap_normalization, coefficientRootMap_normalization]
  dsimp only [finiteLineTransition]
  erw [(finiteLineTransition_existsUnique T l A r n hrn hr hn hTr).choose_spec.1]
  have h := restriction_power T (l ^ (r + 1)) (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
    (pow_dvd_pow l (Nat.succ_le_succ hrn)) q hq
  exact congrArg (fun z ↦ Scheme.tateFiniteTensor T l A r
    (Scheme.finiteEtaleTwistScalar _ A hr) ((Scheme.toProEt T).obj W.unop)
    (coefficientSection T A ((Scheme.toProEt T).op.obj W) 1) z)
      (congrArg (fun f ↦ f.hom.app W z) h).symm

/-- Power transitions identify the Kummer classes at any two admissible levels.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv).
Proof: for r<=n map the exponent-l^(n+1) Kummer sequence to the smaller one by
the l^(n-r) power on the middle units, identity on the right units, and the power
transition on roots. Naturality of boundaries identifies the two root classes.
The coefficient and site comparisons commute with these root powers by their
pure-tensor normalizations. This proves the equality. For any two indices choose
the larger; their comparison is this isomorphism or its inverse. -/
theorem kummer_exponent_independent (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hTr : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hTn : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    Sheaf.H.map (finiteLineTransition T l A r n hrn hr hn hTr).hom 1
      (kummer T l A n hn hTn v) = kummer T l A r hr hTr v := by
  have hd := pow_dvd_pow l (Nat.succ_le_succ hrn)
  obtain ⟨q, hq⟩ := roots_power_exists T (l ^ (r + 1)) (l ^ (n + 1)) hd
  have hc := coefficientRootMap_power T l A r n hrn hr hn hTr hTn q hq
  have hδ := boundary_power T (l ^ (r + 1)) (l ^ (n + 1)) hd hTr hTn q hq v
  let x := ProEtale.comparisonCohomologyMap T _ 1
    (T.kummerδ₀ (l ^ (n + 1)) hTn (Additive.ofMul v))
  calc
    _ = Sheaf.H.map (coefficientRootMap T l A n hn hTn ≫
        (finiteLineTransition T l A r n hrn hr hn hTr).hom) 1 x := by
      simp only [kummer, coefficientRootMap, Sheaf.H.map_comp_apply,
        ProEtale.comparisonCohomologyMap, Sheaf.H.mapFunctor_map, x]
    _ = Sheaf.H.map ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map q ≫
        coefficientRootMap T l A r hr hTr) 1 x := by rw [hc]
    _ = _ := by
      rw [Sheaf.H.map_comp_apply]
      dsimp [x]
      rw [ProEtale.comparisonCohomologyMap, ← Sheaf.H.mapFunctor_map, hδ]
      simp only [coefficientRootMap, kummer, Sheaf.H.map_comp_apply,
        ProEtale.comparisonCohomologyMap, Sheaf.H.mapFunctor_map]

/-- The concrete root torsor is the torsor of lifts of the unit in the Kummer sequence.
Its underlying sections are exactly local units whose l^(r+1)-th power is v.
Source: blueprint sk-def-purity-conv, torsor interpretation
(blueprint: sk-def-purity-conv). -/
def rootTorsor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    Sheaf.Torsor (T.rootsOfUnitySheaf (l ^ (r + 1))) :=
  Sheaf.Torsor.lifts (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
    (T.kummerSequence_shortExact (l ^ (r + 1)) hT) (ULift.up (Additive.ofMul v))

/-- The actual relative root cover, constructed by the existing monic quotient algebra.
Source: blueprint sk-def-purity-conv, relative spectrum T_t
(blueprint: sk-def-purity-conv). -/
abbrev rootCover (T : Scheme.{u}) (l r : ℕ) (v : Γ(T, ⊤)ˣ) : Scheme.{u} :=
  T.kummerCover (l ^ (r + 1)) (v : Γ(T, ⊤))

private theorem homSpecEquiv_precomp {V W : Scheme.{u}} (f : V ⟶ W)
    (R : CommRingCat.{u}) (g : W ⟶ Spec R) :
    Scheme.homSpecEquiv V R (f ≫ g) = Scheme.homSpecEquiv W R g ≫ f.appTop := by
  change ((ΓSpec.adjunction.homEquiv V (op R)).symm (f ≫ g)).unop = _
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

private theorem kummerCoverHomEquiv_precomp {T V W : Scheme.{u}} (n : ℕ)
    (v : Γ(T, ⊤)) (h : W ⟶ T) (f : V ⟶ W)
    (hV : V ⟶ T) (hw : f ≫ h = hV)
    (a : {a : W ⟶ T.kummerCover n v // a ≫ T.kummerCoverπ n v = h}) :
    ((Scheme.kummerCoverHomEquiv n v hV)
      ⟨f ≫ a.val, by rw [Category.assoc, a.property, hw]⟩).val =
      f.appTop ((Scheme.kummerCoverHomEquiv n v h a).val) := by
  change (Scheme.homSpecEquiv V _ ((f ≫ a.val) ≫ pullback.snd _ _))
      (AdjoinRoot.root _) = _
  rw [Category.assoc, homSpecEquiv_precomp]
  rfl

private def rootTorsorUnitsEquiv (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) (W : T.Etale) :
    (rootTorsor T l r hT v).sheaf.obj.obj (op W) ≃
      {w : Γ(W.left, ⊤)ˣ // w ^ (l ^ (r + 1)) = Units.map W.hom.appTop.hom.toMonoidHom v} :=
  Equiv.subtypeEquiv (Scheme.gmSheafSectionsEquiv W) fun x ↦ by
    change (l ^ (r + 1)) • x =
        T.gmSheaf.obj.map
          ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from W).op
          (ULift.up (Additive.ofMul v)) ↔ _
    have hw :
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from W =
          MorphismProperty.Over.homMk W.hom := by
      apply Subsingleton.elim
    rw [hw]
    change (l ^ (r + 1)) • x =
      ULift.up (Additive.ofMul (Units.map W.hom.appTop.hom.toMonoidHom v)) ↔ _
    exact (Scheme.gmSheafSectionsEquiv W).injective.eq_iff.symm

/-- The root torsor is represented by the specified root cover, naturally on etale objects.
Source: blueprint sk-def-purity-conv, torsor equation
(blueprint: sk-def-purity-conv).
Proof: on an affine open the universal property of R[T0]/(T0^l^(r+1)-v) identifies
maps into its spectrum with roots of v. A root is a unit because its positive power
is the unit v. These local identifications commute with ring restriction and hence
glue to the displayed natural bijections for every etale object. The lifting torsor
uses precisely the same root equation. The action is multiplication by a root of
unity, which is addition of its image in the additive units sheaf. -/
theorem rootTorsor_represented (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    ∃ e : ∀ W : T.Etale, (rootTorsor T l r hT v).sheaf.obj.obj (op W) ≃
        {a : W.left ⟶ rootCover T l r v //
          a ≫ T.kummerCoverπ (l ^ (r + 1)) (v : Γ(T, ⊤)) = W.hom},
      ∀ (V W : T.Etale) (f : V ⟶ W)
        (x : (rootTorsor T l r hT v).sheaf.obj.obj (op W)),
        (e V ((rootTorsor T l r hT v).sheaf.obj.map f.op x)).val =
          f.left ≫ (e W x).val := by
  let : NeZero (l ^ (r + 1)) := ⟨ne_of_gt (pow_pos (Fact.out : l.Prime).pos _)⟩
  let e (W : T.Etale) :=
    (rootTorsorUnitsEquiv T l r hT v W).trans
      ((Scheme.unitsPowEqEquiv (l ^ (r + 1)) (Units.map W.hom.appTop.hom.toMonoidHom v)).trans
        (Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom).symm)
  refine ⟨e, ?_⟩
  intro V W f x
  suffices heq : e V ((rootTorsor T l r hT v).sheaf.obj.map f.op x) =
      ⟨f.left ≫ (e W x).val, by rw [Category.assoc, (e W x).property,
        MorphismProperty.Over.w f]⟩ from congrArg Subtype.val heq
  apply (Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) V.hom).injective
  apply Subtype.ext
  have hnat := kummerCoverHomEquiv_precomp (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom
    f.left V.hom (MorphismProperty.Over.w f) (e W x)
  have he (W : T.Etale) (x : (rootTorsor T l r hT v).sheaf.obj.obj (op W)) :
      ((Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom)
        (e W x)).val = x.val.down.toMul.val := by
    exact congrArg Subtype.val
      ((Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom).apply_symm_apply _)
  rw [he] at hnat
  rw [he]
  exact hnat.symm

/-- Extending the root torsor by the specified coefficient insertion gives the class kappa.
Source: blueprint sk-def-purity-conv, equivalent torsor description
(blueprint: sk-def-purity-conv).
Proof: the root torsor is the sheaf of lifts in the Kummer exact sequence, so its
canonical class is the boundary of v by classH1_lifts. On every affine chart the
same root equation represents this sheaf by O[T0]/(T0^l^(r+1)-v), hence by the
published kummerCover. Coefficient functoriality of the torsor classification
identifies the contracted-product class with H1 of insertion applied to this
boundary. Applying comparison and the normalized coefficient identification gives
exactly the defining composite of kummer. -/
theorem kummer_torsor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    ∃ S : Sheaf.Torsor ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
        (coefficientModule A (l ^ (r + 1)) hA)),
      Nonempty (Sheaf.Torsor.ContractedProductPresentation T
        (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
          (coefficientModule A (l ^ (r + 1)) hA) (1 : A))
        (rootTorsor T l r hT v) S) ∧
      Sheaf.H.map (coefficientComparison T l A r hA hT).hom 1
        (ProEtale.comparisonCohomologyMap T _ 1
          (Sheaf.Torsor.classH1 _ terminalIsTerminal ⟦S⟧)) =
        kummer T l A r hA hT v := by
  obtain ⟨S, hS, hclass⟩ := Sheaf.Torsor.etale_torsor_h1_functoriality.2 T _ _
    (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
      (coefficientModule A (l ^ (r + 1)) hA) (1 : A)) (rootTorsor T l r hT v)
  refine ⟨S, hS, ?_⟩
  have hroot : Sheaf.Torsor.classH1 _ terminalIsTerminal ⟦rootTorsor T l r hT v⟧ =
      T.kummerδ₀ (l ^ (r + 1)) hT (Additive.ofMul v) := by
    exact (Sheaf.Torsor.classH1_congr
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
      terminalIsTerminal _).trans (Sheaf.Torsor.classH1_lifts _ _ _)
  rw [← hclass, hroot]
  rfl

/-- Every positive power of the coefficient prime is a unit on a k-scheme.
Source: blueprint sk-def-purity-conv, invertibility convention
(blueprint: sk-def-purity-conv).
Proof: ell differs from the characteristic of the fixed field k, hence is a unit
in k. Take its r+1 power and map along the structure morphism on global sections.
The argument includes the empty scheme. -/
theorem coefficientPower_isUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
  have hl : IsUnit ((P.coefficients.l : Γ(T, ⊤)) ^ P.level) := by
    simpa only [PurityFiniteSetting.diagonalExponent, Nat.cast_pow] using
      P.diagonalExponent_isUnit a
  simpa only [Nat.cast_pow] using
    ((isUnit_pow_iff (Nat.ne_of_gt P.level_pos)).mp hl).pow (r + 1)

/-- N=n is always an admissible annihilator, even when e does not divide n.
The predecessor index represents exactly n because level_pos gives n>=1.
Source: blueprint sk-def-purity-conv, default Kummer level
(blueprint: sk-def-purity-conv).
Proof: diagonalExponent_annihilates gives ell^n=0 in the quotient and its lift.
Use (n-1)+1=n, following from level_pos. In the DVR the underlying containment
is (ell^n) subset (varpi^n), since the ramification index is at least one. -/
theorem defaultAnnihilator (P : PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ (P.level - 1 + 1) : ℕ) : P.Coefficient) = 0 := by
  simpa only [Nat.sub_add_cancel P.level_pos, PurityFiniteSetting.diagonalExponent] using
    P.diagonalExponent_annihilates

/-- The rank-one datum kappa(t) of the actual affine coordinate, at N=n.
No ramification-divisibility hypothesis is imposed. The affine line, its zero
section, complement, and coordinate unit are the recorded constructions.
Source: blueprint sk-def-purity-conv, rank-one datum
(blueprint: sk-def-purity-conv). -/
def coordinateKummer (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    Sheaf.H (finiteLine (PurityFiniteSetting.Punctured Y) P.coefficients.l P.Coefficient
      (P.level - 1) (defaultAnnihilator P)) 1 :=
  kummer (PurityFiniteSetting.Punctured Y) P.coefficients.l P.Coefficient (P.level - 1)
    (defaultAnnihilator P)
    (coefficientPower_isUnit P (PurityFiniteSetting.Punctured Y)
      (PurityFiniteSetting.puncturedProjection Y ≫ aY) (P.level - 1))
    (PurityFiniteSetting.coordinateUnit Y)

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
      exact inferInstanceAs (IsIso ((SheafOfModules.forget _).map
        ((commAlgebraSheafModuleFunctor Z.sheaf).map f)))
    have happ (W : Z.Opensᵒᵖ) : IsIso (f.right.hom.app W) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      have : IsIso (((commAlgebraSheafModuleFunctor Z.sheaf).map f).val.app W) := by
        exact inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ W).map
          ((commAlgebraSheafModuleFunctor Z.sheaf).map f).val))
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
