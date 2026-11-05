/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization
import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProetaleSiteProperties

/-! # Restriction squares for a fixed normalized integral section comparison

Source: blueprint integral-criterion-reductions, final interpretation; Stacks 00YV and 03EK.
(blueprint: lem-pe-fixed-integral-section-squares).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
attribute [local irreducible] upperStarFromPoint
  InternalAbelianSheafModule.sectionScalarMap

private def restrictComp
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        ((f ≫ g).hom.app U).hom rfl (M.val.obj U)).symm)
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private theorem restrictComp_hom_forget
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T)
    (M : SheafOfModules.{u + 1} T) :
    (SheafOfModules.toSheaf R).map ((restrictComp f g).hom.app M) =
      𝟙 ((SheafOfModules.toSheaf T).obj M) := by
  ext V x
  rfl

private theorem restrictComp_inv_forget
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T)
    (M : SheafOfModules.{u + 1} T) :
    (SheafOfModules.toSheaf R).map ((restrictComp f g).inv.app M) =
      𝟙 ((SheafOfModules.toSheaf T).obj M) := by
  ext V x
  rfl

private theorem restrict_map_forget
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (f : R ⟶ S)
    {M N : SheafOfModules.{u + 1} S} (a : M ⟶ N) :
    (SheafOfModules.toSheaf R).map ((SheafOfModules.restrictScalars f).map a) =
      (SheafOfModules.toSheaf S).map a := rfl

private theorem restrict_cast_forget
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (f g : R ⟶ S)
    (M : SheafOfModules.{u + 1} S)
    (h : (SheafOfModules.restrictScalars f).obj M =
      (SheafOfModules.restrictScalars g).obj M) :
    (SheafOfModules.toSheaf R).map (eqToHom h) =
      𝟙 ((SheafOfModules.toSheaf S).obj M) := by
  rw [eqToHom_map]
  exact eqToHom_refl _ _

private theorem sectionRestriction_forget
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {R S : Sheaf J Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (M : Mod (Sheaf J Ab.{u + 1}) S) :
    (SheafOfModules.toSheaf ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))).map
      ((InternalAbelianSheafModule.scalarRestrictionIso.{u + 1, u + 1, u} J a).hom.app M) =
      𝟙 M.X := by
  ext V x
  rfl

private theorem normalizedSquare
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {R S : Sheaf J Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    {T V : Sheaf J RingCat.{u + 1}}
    (r : T ⟶ (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))
    (p : T ⟶ V)
    (c : V ⟶ (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S))
    (hq : r ≫ (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J a) = p ≫ c)
    (F : Mod (Sheaf J Ab.{u + 1}) R ⥤ SheafOfModules.{u + 1} T)
    (G : Mod (Sheaf J Ab.{u + 1}) S ⥤ SheafOfModules.{u + 1} V)
    (hF : F = (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      J R).functor ⋙ SheafOfModules.restrictScalars r)
    (hG : G = (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      J S).functor ⋙ SheafOfModules.restrictScalars c) :
    ∃ α : Mod.comap a ⋙ F ≅ G ⋙ SheafOfModules.restrictScalars p,
      ∀ M, (SheafOfModules.toSheaf T).map (α.hom.app M) =
        (SheafOfModules.toSheaf T).map
            (eqToHom (congrArg (fun H ↦ H.obj ((Mod.comap a).obj M)) hF)) ≫
          (SheafOfModules.toSheaf V).map
            (eqToHom (congrArg (fun H ↦ H.obj M) hG.symm)) := by
  subst F
  subst G
  let q := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J a)
  let β : SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars r ≅
      SheafOfModules.restrictScalars c ⋙ SheafOfModules.restrictScalars p :=
    restrictComp r q ≪≫ eqToIso
      (congrArg (fun k ↦ SheafOfModules.restrictScalars k) hq) ≪≫ (restrictComp p c).symm
  let α := Functor.isoWhiskerRight
      (InternalAbelianSheafModule.scalarRestrictionIso.{u + 1, u + 1, u} J a)
      (SheafOfModules.restrictScalars r) ≪≫
    Functor.isoWhiskerLeft
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J S).functor β
  refine ⟨α, ?_⟩
  intro M
  simp only [α, β, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToIso.hom,
    eqToHom_app, Iso.symm_hom, Functor.map_comp, restrict_map_forget,
    sectionRestriction_forget, restrictComp_hom_forget, restrictComp_inv_forget,
    eqToHom_refl]
  simp only [restrict_cast_forget]
  ext W x
  rfl

/-- Every specified normalized integral coefficient comparison has the normalized
finite restriction squares; the integral comparison is not chosen anew.
Source: blueprint integral-criterion-reductions, final interpretation; Stacks 00YV and 03EK
(blueprint: lem-pe-fixed-integral-section-squares).

Proof: at each positive level choose the normalized finite discrete encoding. The
mate equation in SfbIntegralComparison identifies the integral map followed by its
nth projection with the continuous quotient map on profinite tests. The point
adjunction and Yoneda give the equality of abelian sheaf maps, and faithfulness of
forgetting ring structure gives equality of ring maps. On a finite-level module,
restriction along these equal composites therefore gives identical integral scalar
actions. The identity on its abelian sections is linear and natural, and its inverse
is the same identity. This gives the restriction square. Forgetting its module
structure yields exactly the two recorded section-functor equality transports,
which is SquareNormalized. No completeness or constructibility is used. -/
theorem fixed_integral_section_squares
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (A : Encoding l E X)
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (he : SfbIntegralComparison l E X e)
    (hsrc : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)) =
        (coefficientRing X (sfbCondensedIntegers l E)).X)
    (htgt : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) =
        sfbCompletedIntegersAb l E X)
    (hc : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map A.ringIso.hom =
          eqToHom hsrc ≫ e.hom ≫ eqToHom htgt.symm) :
    ∃ (f : ∀ n : ℕ, FiniteEncoding l E X n)
      (a : ∀ n : ℕ, RestrictionSquare l E X A n (f n)),
      ∀ n : ℕ, SquareNormalized l E X A n (f n) (a n) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨A₀, f, a₀, ha₀⟩ := integral_completion_normalized_squares l E X
  have hproj (n : ℕ) := integral_section_projection_normalization
    l E X A e he hsrc htgt hc n (f n)
  let J := Scheme.ProEt.topology X
  let U := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let r := U.map A.ringIso.inv
  let qₙ (n : ℕ) := InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J
    (AdicCompletion.quotient l E X n)
  let cₙ (n : ℕ) := U.map (f n).ringIso.hom
  let pₙ (n : ℕ) := U.map
    (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n)
  have hq (n : ℕ) : r ≫ U.map (qₙ n) = pₙ n ≫ cₙ n := by
    dsimp only [r, qₙ, pₙ, cₙ]
    rw [hproj, Functor.map_comp, Functor.map_comp, ← U.map_comp_assoc,
      Iso.inv_hom_id, U.map_id, Category.id_comp]
  have hs (n : ℕ) := normalizedSquare (Scheme.ProEt.topology X)
    (AdicCompletion.quotient l E X n) r (pₙ n) (cₙ n) (hq n)
    A.modules.functor (f n).ordinary.functor A.functor_eq (f n).ordinary_functor
  choose a ha using hs
  refine ⟨f, a, ?_⟩
  intro n M
  have h := ha n M
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_map] at h ⊢
  exact h

end AlgebraicGeometry.ProEtale.IntegralPresentation
