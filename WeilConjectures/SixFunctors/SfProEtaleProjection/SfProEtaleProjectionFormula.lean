/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import Mathlib.Algebra.CharP.Invertible
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionConservative
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionReduction
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperProjectionFormulaBounded
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitLocality
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The finite and condensed pro-etale projection formulas

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-pf-proetale,
statement and proof (blueprint: sk-thm-sf-pf-proetale).

`sf_proetale_projection_formula` proves invertibility of the canonical projection
for arbitrary finite admissible coefficients with retained etale origins, and for
the condensed rings O_E, E and Qbar_l on separated finite-type schemes.

`SfProEtaleProjection.Origin` records the fixed-scalar etale-origin witness and
its intrinsic realization. The finite proof transports this witness and the Tor
interval to the existing finite-ring projection theorem. The condensed proof uses
the proper projection theorem, inverse open tensor comparison, and pullback
composition isomorphism of the existing proper/open projection map.

The integral compatibility definitions `ordinarySource`, `ordinaryInner`,
`completedSource`, `completedTarget`, `integralDomains` and `integralMap` remain
available to their existing consumers. They concern the earlier completed-tower
model; no identification of that model with condensed coefficients is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace SfProEtaleProjection

/-- A retained bounded constructible etale origin in the recorded fixed-scalar
presentation, together with the canonical intrinsic realization of its target.
This packages the existing witness; it does not choose a new inverse image.
Source: blueprint finite-coefficient clause and def-weil-pbc-etale-origin-witness
(blueprint: sk-thm-sf-pf-proetale). -/
structure Origin (W : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (K : proEtaleDerivedCategory W R) where
  object : DerivedCategory.Plus
    (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))
  witness : FixedEtaleOriginWitness W (ULift.{u + 1, u} R) object
  constructible : Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} R) W witness.complex.obj
  realization : (sfIntrinsicModuleEquivalence W R).functor.mapDerivedCategory.obj
    object.obj ≅ K

attribute [local irreducible] ordinaryIntegralModulePull ordinaryIntegralModuleAdjunction
  ordinaryIntegralDirectRingMap
  integralCompletedTensor integralOperationsTensorComplexFunctor
  IntegralOnSlice.completion IntegralOnSlice.completionUnit
  constructibleTensorTotalSection integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection
  HasProEtaleTorAmplitude

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing signed K-flat tensor model over the completed coefficient sheaf.
Source: blueprint integral coefficient clause; Stacks 07A4
(blueprint: sk-thm-sf-pf-proetale). -/
abbrev TensorModel (W : Scheme.{u}) :=
  ProEtaleTensorModel W ((PurCompactSupport.completed l E).ring W)

private theorem goodRepresentative (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
    ∃ P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  have := Localization.essSurj (DerivedCategory.Q (C := integralTowerModules.{u, u} l E W))
    (HomologicalComplex.quasiIso _ (.up ℤ))
  let L := (DerivedCategory.Q (C := integralTowerModules.{u, u} l E W)).objPreimage K
  let e := (DerivedCategory.Q (C := integralTowerModules.{u, u} l E W)).objObjPreimageIso K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) L
  let : QuasiIso f := hf
  let : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (integralTowerModules.{u, u} l E W) f).2 hf
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i) := by
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)).symm (hflat i)
  exact ⟨⟨P, hP, hsite⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e⟩⟩

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall
  constructibleTensorSiteSmall in
private theorem tensor_domains (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] (hl : IsUnit (l : Γ(W, ⊤)))
    (a : TensorModel.{u} l E W) (M N : DerivedCategory (integralTowerModules.{u, u} l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    sfIntegralConstructible l E W (a.tensor.obj (M, N)) ∧
      IsIso ((IntegralOnSlice.completionUnit.{u, u} l E W none).app (a.tensor.obj (M, N))) ∧
      sfIntegralConstructible l E W
        ((IntegralOnSlice.completion.{u, u} l E W none).obj (a.tensor.obj (M, N))) := by
  have presentation := @constructibleTensorCompletion.{u} l _ E _ _ _ W
    ‹CompactSpace W› ‹QuasiSeparatedSpace W› ‹∀ w : W, Invertible (l : W.residueField w)›
  let T := presentation.choose
  let e := presentation.choose_spec.choose
  let hchi := presentation.choose_spec.choose_spec.choose_spec
  let tau := hchi.2.2.choose
  have ht := hchi.2.2.choose_spec.2
  obtain ⟨P, ⟨p⟩⟩ := goodRepresentative.{u} l E W M
  obtain ⟨Q, ⟨q⟩⟩ := goodRepresentative.{u} l E W N
  have hP : proEtaleFlatRepresentatives.{u} W ((PurCompactSupport.completed.{u} l E).ring W)
      P.obj := P.property
  have hQ : proEtaleFlatRepresentatives.{u} W ((PurCompactSupport.completed.{u} l E).ring W)
      Q.obj := Q.property
  let z : a.tensor.obj (M, N) ≅ T.obj (M, N) :=
    a.tensor.mapIso (Iso.prod p q).symm ≪≫
      (a.representative.app (⟨P.obj, hP⟩, ⟨Q.obj, hQ⟩)).symm ≪≫
      e.app (P, Q) ≪≫ T.mapIso (Iso.prod p q)
  have hi := (ht M N hM hN).2
  have hT : sfIntegralConstructible l E W (T.obj (M, N)) :=
    (sfIntegralConstructible l E W).prop_of_iso (asIso (tau.app (M, N))).symm
      ((integralOperations_preserve_constructible l E (𝟙 W)).2 W (Or.inl rfl)
        M N hM hN).1
  have hA := (sfIntegralConstructible l E W).prop_of_iso z.symm hT
  have hunitT : IsIso ((IntegralOnSlice.completionUnit.{u, u} l E W none).app (T.obj (M, N))) :=
    ((IntegralOnSlice.qcqsCompletionUnitLocality.{u, u, u} l E W hl).1 _).mpr (ht M N hM hN).1
  have hz := (IntegralOnSlice.completionUnit.{u, u} l E W none).naturality z.hom
  have hunit : IsIso ((IntegralOnSlice.completionUnit.{u, u} l E W none).app
      (a.tensor.obj (M, N))) := by
    have hc : IsIso ((IntegralOnSlice.completionUnit.{u, u} l E W none).app
        (a.tensor.obj (M, N)) ≫ (IntegralOnSlice.completion.{u, u} l E W none).map z.hom) := by
      rw [← hz]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((IntegralOnSlice.completion.{u, u} l E W none).map z.hom)
  exact ⟨hA, hunit, (sfIntegralConstructible l E W).prop_of_iso
    (asIso ((IntegralOnSlice.completionUnit.{u, u} l E W none).app (a.tensor.obj (M, N)))) hA⟩

private theorem pull_domains {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    (hXd : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hYd : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hXi : IsUnit (l : Γ(X, ⊤))) (hYi : IsUnit (l : Γ(Y, ⊤)))
    (L : DerivedCategory (integralTowerModules l E Y)) (hL : sfIntegralConstructible l E Y L) :
    sfIntegralConstructible l E X
      ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L) := by
  have hmap : (⟨Functor.whiskerRight (sfCompletedCoefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
        completedIntegralCoefficientSheafUnrestricted l E Y ⟶
          (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
            (completedIntegralCoefficientSheafUnrestricted l E X)) =
      ordinaryIntegralDirectRingMap l E f := by
    apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
    · intro n
      exact congrArg ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        ((sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n)
    · simpa only [ordinaryIntegralDirectRingMap] using
        (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec
  have hadj : proEtaleRingDirectImageMap f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f := by
    exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  let e : proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) ≅ ordinaryIntegralModulePush l E f := by
    unfold proEtaleRingModuleDirectImage ordinaryIntegralModulePush
    rw [hadj]
    exact SheafOfModules.pushforwardCongr hmap
  let a := (proEtaleRingModuleAdjunction f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).ofNatIsoRight e
  let b := a.leftAdjointUniq (ordinaryIntegralModuleAdjunction l E f)
  have := preservesFiniteLimits_of_natIso b
  have := ordinaryIntegralModulePull_additive l E f
  have := (ordinaryIntegralModuleAdjunction l E f).leftAdjoint_preservesColimits
  let d := Functor.mapDerivedCategoryNatIso b
  let F := ordinaryIntegralModulePull l E f
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh
  let : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f)
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
    unfold ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
    infer_instance
  let c : ordinaryIntegralDerivedPull l E f ≅ F.mapDerivedCategory :=
    Functor.leftDerivedUnique F.mapDerivedCategory (ordinaryIntegralDerivedPull l E f)
      (ordinaryIntegralPullCounit l E f) F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))
  exact (sfIntegralConstructible l E X).prop_of_iso
    (d.app L ≪≫ (c.app L).symm).symm
    (ordinaryCompletedIntegralPullback l E f hXd hYd hXi hYi L hL).1

/-- Ordinary presentation of the completed projection's source before its unit.
Source: blueprint projection display (blueprint: sk-thm-sf-pf-proetale). -/
def ordinarySource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aY : TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  aY.tensor.obj ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K, L)

/-- Ordinary tensor inside the compact-support projection's target.
Its completion also computes completed tensor with completed pullback: inserting
that factor's completion unit becomes invertible after tensor completion.
Source: blueprint projection display; Stacks 099N
(blueprint: sk-thm-sf-pf-proetale). -/
def ordinaryInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  aX.tensor.obj (K, (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L)

/-- The completed tensor on the source of the projection.
The completion and unit are the actual positive-quotient Roos construction.
Source: blueprint integral clause; Bhatt--Scholze Definition 3.4.10
(blueprint: sk-thm-sf-pf-proetale). -/
def completedSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aY : TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  (IntegralOnSlice.completion l E Y none).obj (ordinarySource l E c aY K L)

/-- Compact support of the completed tensor on the target of the projection.
Source: blueprint integral clause; Bhatt--Scholze Definition 3.4.10
(blueprint: sk-thm-sf-pf-proetale). -/
def completedTarget {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
    ((IntegralOnSlice.completion l E X none).obj (ordinaryInner l E f aX K L))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

include hl in
/-- The coefficient prime is a unit already in the base field: its characteristic is
`D.p`, and two distinct primes do not divide one another. This is a direct Mathlib
specialization and uses no compact-support coefficient comparison. -/
private theorem coefficient_unit : IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact (CharP.isUnit_natCast_iff D.prime).2
    (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).mp h).symm)

include hl in
private theorem scheme_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    IsUnit (l : Γ(W, ⊤)) := by
  let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
  simpa only [map_natCast] using (coefficient_unit l D hl).map ρ.hom

include hl in
private theorem residue_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (w : W) :
    IsUnit (l : W.residueField w) := by
  let ρ := W.presheaf.germ ⊤ w trivial
  have hs := (scheme_unit l D hl W).map ρ.hom
  exact (by simpa only [map_natCast] using hs.map (W.residue w).hom)

private theorem finite_dimension (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))] :
    ∃ n : ℕ, topologicalKrullDim W ≤ n := by
  have hd := topologicalKrullDim_lt_top_of_finiteType (W ↘ Spec (.of D.k))
  obtain h | h := eq_or_ne (topologicalKrullDim W) ⊥
  · exact ⟨0, by simp only [h, bot_le]⟩
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h
    rw [← ha] at hd ⊢
    change (a : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) at hd
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_lt_coe.mp hd).ne
    exact ⟨n, by rw [← hn]; exact le_rfl⟩

include D hl in
/-- Typing facts for the canonical completed projection, without structural
separatedness assumptions on X or Y. They hold for every integral constructible
representative; thus raw rationalization has no additional lattice restriction.
Source: blueprint proof steps 1, 3, 4; Bhatt--Scholze Sections 6.5 and 6.7
(blueprint: sk-thm-sf-pf-proetale).

Proof: finite type over the field gives Noetherianness, quasi-compactness, and
finite dimension; the coefficient prime is invertible in global sections and residue
fields. The normalized compact-support realization preserves integral constructibility.
Compare each supplied tensor model with the ordinary signed K-flat tensor of
`constructibleTensorCompletion` on good representatives. Its completion comparison
and integral completed-tensor constructibility give constructibility of the ordinary
tensor. The completion-unit criterion then gives invertibility of its canonical unit
and constructibility of its completion. For the inner tensor, identify the specified
ordinary pullback with `ordinaryIntegralDerivedPull` by their scalar maps and the
uniqueness of left adjoints and left derived functors; ordinary/completed pullback
preserves constructibility. Apply the tensor argument on X and compact support again.
No separatedness of either structure morphism is used. -/
theorem integralDomains
    (aX : TensorModel l E X) (aY : TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    IsIso ((IntegralOnSlice.completionUnit l E Y none).app
      (ordinarySource l E c aY K.obj L.obj)) ∧
    sfIntegralConstructible l E Y (completedSource l E c aY K.obj L.obj) ∧
    sfIntegralConstructible l E Y (completedTarget l E c aX K.obj L.obj) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (residue_unit l D hl X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (residue_unit l D hl Y y).invertible
  have support (M : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj M.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E D.k
        (coefficient_unit l D hl) c).app M).symm
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (coefficient_unit l D hl) c E).obj M).property
  have ht := tensor_domains l E Y (scheme_unit l D hl Y) aY _ _ (support K) L.property
  refine ⟨ht.2.1, ht.2.2, ?_⟩
  have hp := pull_domains l E f (finite_dimension D X) (finite_dimension D Y)
    (scheme_unit l D hl X) (scheme_unit l D hl Y) L.obj L.property
  have hi := tensor_domains l E X (scheme_unit l D hl X) aX _ _ K.property hp
  exact support ⟨_, hi.2.2⟩

/-- The actual completed projection in the intrinsic completed category.
It is the unique extension of the ordinary proper-counit/open projection across
its source completion unit. The target unit is applied before compact support.
Thus eta_source followed by this map equals ordinary PF followed by Rf! eta_inner.
This is precisely the completed-adjunction normalization of def-exchange-projection;
no projection arrow or arbitrary isomorphism is supplied as an input.
Source: blueprint projection display; Stacks 099N; completed projection unit equation
(blueprint: sk-thm-sf-pf-proetale). -/
def integralMap
    (aX : TensorModel l E X) (aZ : TensorModel l E c.Z) (aY : TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    (⟨completedSource l E c aY K.obj L.obj,
      (integralDomains l E D hl f c aX aY K L).2.1⟩ :
        sfIntegralConstructibleCategory l E Y) ⟶
    (⟨completedTarget l E c aX K.obj L.obj,
      (integralDomains l E D hl f c aX aY K L).2.2⟩ :
        sfIntegralConstructibleCategory l E Y) :=
  letI := (integralDomains l E D hl f c aX aY K L).1
  ObjectProperty.homMk
    (inv ((IntegralOnSlice.completionUnit l E Y none).app
        (ordinarySource l E c aY K.obj L.obj)) ≫
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj) ≫
      (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
        ((IntegralOnSlice.completionUnit l E X none).app
          (ordinaryInner l E f aX K.obj L.obj)))

private theorem integral_isIso
    (aX : TensorModel l E X) (aZ : TensorModel l E c.Z) (aY : TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    IsIso (integralMap l E D hl f c aX aZ aY K L) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (residue_unit l D hl X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (residue_unit l D hl Y y).invertible
  have support (M : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj M.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E D.k
        (coefficient_unit l D hl) c).app M).symm
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (coefficient_unit l D hl) c E).obj M).property
  have hs := tensor_domains l E Y (scheme_unit l D hl Y) aY _ _ (support K) L.property
  have hp := pull_domains l E f (finite_dimension D X) (finite_dimension D Y)
    (scheme_unit l D hl X) (scheme_unit l D hl Y) L.obj L.property
  have hi := tensor_domains l E X (scheme_unit l D hl X) aX _ _ K.property hp
  let P := ((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
    (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj
  have hP : IsIso P := sfIntegralReduction_conservative l E Y P hs.1
    (support ⟨_, hi.1⟩)
    (integralOrdinaryProjection_finiteReductions D l hl E f c aX aZ aY K L)
  let := hP
  let : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (ordinaryInner l E f aX K.obj L.obj)) := hi.2.1
  let : IsIso ((IntegralOnSlice.completionUnit l E Y none).app
      (ordinarySource l E c aY K.obj L.obj)) :=
    (integralDomains l E D hl f c aX aY K L).1
  apply (ObjectProperty.isIso_hom_iff _).mp
  change IsIso (inv _ ≫ P ≫ (PurCompactSupport.image _ c).map _)
  infer_instance

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

attribute [local irreducible] sfIntrinsicModuleEquivalence
  finiteRingCompactSupportProjection ProEtale.projectionMapOfCompactification

end SfProEtaleProjection

attribute [local irreducible] sfIntrinsicModuleEquivalence
  finiteRingCompactSupportProjection ProEtale.projectionMapOfCompactification
  ProEtale.derivedTensorRightDerivedLowerShriek HasProEtaleTorAmplitude

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
private theorem projection_iso_of_property
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : ProEtale.HasProjectionFormulaOfCompactification A c K L) :
    IsIso (((ProEtale.projectionMapOfCompactification A c).app K).app L) := h

/-- The compact-support projection formula for arbitrary finite admissible coefficients,
and directly for condensed integral, field and algebraic-closure coefficients.

Source: current blueprint part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-thm-sf-pf-proetale/thm-sf-pf-proetale.md, all clauses, with the standing setting of its
parent unit (blueprint: thm-sf-pf-proetale).

Proof: retain etale antecedents M,H and their specified comparison isomorphisms. For the
chosen compactification f = r j, exact j_! preserves a lower bound for M and pullback
preserves the Tor interval of H. Tensor symmetry and the Tor estimate bound
j_!M tensor r^*H below. The etale compactification projection is the proper counit
projection followed by proper pushforward of the open tensor comparison; both factors
are invertible for every finite admissible ring. Paste the proper projection comparison
square with the open tensor square. The intermediate comparisons cancel and identify
this transported composite with the specified pro-etale projection map, including the
compact-support comparison normalization. All comparison maps are invertible, so the
pro-etale projection is invertible. Conjugate also by the retained origin isomorphisms;
this includes witnesses supplied by comparison. The Tor estimate bounds the source
below, and its isomorphic target has the same lower bound, giving an isomorphism in D+.
For O_E, E and Qbar_ell, work directly with bounded constructible internal modules (the
clauses that thm-sf-pf-adic and thm-sf-pf-field record): extension by zero along the open
immersion of c keeps K bounded constructible, the native proper projection formula of the
condensed coefficients makes the proper factor invertible, and the remaining factor of the
compactification projection is a canonical isomorphism.
There is no etale-origin requirement on these non-finite inputs.
-/
theorem _root_.WeilConjectures.sf_proetale_projection_formula
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left) :
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
        (_hA : ∃ n : ℕ, (ell ^ n : A) = 0)
        (K : DerivedCategory.Plus
          (Sheaf (ProEt.topology X.left) (ModuleCat.{u + 1} A)))
        (L : DerivedCategory.Plus
          (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A)))
        (wK : FixedEtaleOriginWitness X.left A K)
        (wL : FixedEtaleOriginWitness Y.left A L)
        (_hK : Etale.DerivedCategory.isBoundedConstructible A X.left wK.complex.obj)
        (_hL : Etale.DerivedCategory.isBoundedConstructible A Y.left wL.complex.obj)
        (_tK : ∃ a b : ℤ,
          Etale.DerivedCategory.hasTorAmplitudeIn A X.left a b wK.complex.obj)
        (_tL : ∃ a b : ℤ,
          Etale.DerivedCategory.hasTorAmplitudeIn A Y.left a b wL.complex.obj),
        ∃ (hS : DerivedCategory.TStructure.t.plus
            (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c).obj
              K.obj).obj L.obj))
          (hT : DerivedCategory.TStructure.t.plus
            (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
              (ModuleCat.{u + 1} A) c).obj K.obj).obj L.obj)),
          IsIso (ObjectProperty.homMk
            (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K.obj).app L.obj) :
            (⟨_, hS⟩ : DerivedCategory.Plus
              (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A))) ⟶ ⟨_, hT⟩)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
        (K : BoundedConstructible
          (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) X.left))
        (L : BoundedConstructible
          (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) Y.left)),
        IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (Profinite.padicIntegersRingObj ell E.1) c K.obj L.obj)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
        (K : BoundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left))
        (L : BoundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)),
        IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (Profinite.continuousMapRingObj E.1) c K.obj L.obj)) ∧
    (∀ (K : BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
        (L : BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ell) Y.left)),
        IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (Profinite.padicAlgClRingObj ell) c K.obj L.obj)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A _ _ _ K L wK wL hK _ _ tL
    obtain ⟨a, b, _, h⟩ := hK.2
    have hM : _root_.DerivedCategory.TStructure.t.bounded wK.complex.obj :=
      ⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2 (fun q hq ↦ h q (.inl hq))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2 (fun q hq ↦ h q (.inr hq))⟩⟩
    obtain ⟨aL, bL, htL⟩ := tL
    have ht := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL
    have hJ := (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hM
    have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hJ ht
    have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
    have hPF : IsIso
        (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K.obj).app L.obj) :=
      hasProjectionFormulaOfCompactification_of_comparison c wK.iso wL.iso hM hML
        inferInstance
    have hR : _root_.DerivedCategory.TStructure.t.plus
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj) :=
      (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).app K)
        ((rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj K).property
    have hLt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y.left aL bL L.obj :=
      (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y.left aL bL).prop_of_iso
        wL.iso ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff aL bL _).mpr ht)
    obtain ⟨r, hr⟩ := hR
    have := hr
    have := _root_.DerivedCategory.isGE_tensor_of_torAmplitudeIn hLt
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj K.obj) r
    let : CategoryTheory.BraidedCategory
        (_root_.DerivedCategory (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A))) :=
      _root_.DerivedCategory.braidedCategory' _
    have hS : _root_.DerivedCategory.TStructure.t.plus
        (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c).obj
          K.obj).obj L.obj) := by
      exact ⟨aL + r, _root_.DerivedCategory.TStructure.t.isGE_of_iso
        (CategoryTheory.BraidedCategory.braiding L.obj
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} A) c).obj K.obj)) (aL + r)⟩
    have hT := (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso
      (asIso (((projectionMapOfCompactification
        (ModuleCat.{u + 1} A) c).app K.obj).app L.obj)) hS
    refine ⟨hS, hT, ?_⟩
    rw [← ObjectProperty.isIso_hom_iff]
    exact hPF
  · intro E K L
    have hJ := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
      (Profinite.padicIntegersRingObj ell E.1) ell c.overI K
    have : IsIso (CondensedRing.properProjectionMorphism
        (Profinite.padicIntegersRingObj ell E.1) c.g
        ((CondensedRing.openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ell E.1) c.i).mapDerivedCategory.obj K.obj) L.obj) :=
      CondensedRing.PadicIntegersRingObj.isIso_properProjectionMorphism
        ell E.1 c.overG _ L.obj hJ L.property
    unfold CondensedRing.exceptionalProjectionMorphismOfCompactification
    infer_instance
  · intro E K L
    have hJ := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
      (Profinite.continuousMapRingObj E.1) ell c.overI K
    have : IsIso (CondensedRing.properProjectionMorphism
        (Profinite.continuousMapRingObj E.1) c.g
        ((CondensedRing.openImmersionLowerShriek
          (Profinite.continuousMapRingObj E.1) c.i).mapDerivedCategory.obj K.obj) L.obj) :=
      CondensedRing.ContinuousMapRingObj.isIso_properProjectionMorphism
        ell E c.overG _ L.obj hJ L.property
    unfold CondensedRing.exceptionalProjectionMorphismOfCompactification
    infer_instance
  · intro K L
    have hJ := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
      (Profinite.padicAlgClRingObj ell) ell c.overI K
    have : IsIso (CondensedRing.properProjectionMorphism
        (Profinite.padicAlgClRingObj ell) c.g
        ((CondensedRing.openImmersionLowerShriek
          (Profinite.padicAlgClRingObj ell) c.i).mapDerivedCategory.obj K.obj) L.obj) :=
      CondensedRing.isIso_properProjectionMorphism_padicAlgCl
        ell c.overG _ L.obj hJ L.property
    unfold CondensedRing.exceptionalProjectionMorphismOfCompactification
    infer_instance

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
attribute [local instance 100000] HasDerivedCategory.standard SheafOfModules.instAbelian

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall in
open scoped CategoryTheory.Obj

attribute [local instance 100] HasDerivedCategory.standard SheafOfModules.instAbelian

end WeilConjectures
