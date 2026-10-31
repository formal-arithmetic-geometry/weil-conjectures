/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.DimensionExtension
import WeilConjectures.AlgebraicGeometry.FinitePointFiniteOrdinaryBound
import WeilConjectures.AlgebraicGeometry.OpenExtensionConstantModelConstructible

/-! The finite compact-support heart bound for a dense compactification. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finite_stratification_models {X : Scheme.{u}}
    (S : Scheme.Stratification X) (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (hP : ∀ t : Fin S.n, P (S.domain t) (S.immersion t)) :
    ∃ T : Scheme.FiniteLocallyClosedStratification X,
      (∀ t : Fin T.n, Topology.IsConstructible (T.stratum t)) ∧
      ∀ t : Fin T.n, P (T.domain t) (T.immersion t) := by
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨T, S.isConstructible_stratum, hP⟩

private theorem open_extension_constructible
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsConstantModelConstructible Λ U M) :
    IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M) := by
  have hqc : CompactSpace U ∧ QuasiSeparatedSpace U :=
    ⟨QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k)),
      quasiSeparatedSpace_of_quasiSeparated (U ↘ Spec (.of k))⟩
  have hstrat : IsFiniteConstantStratified Λ U M := by
    simpa only [IsConstantModelConstructible, if_pos hqc] using hM
  obtain ⟨S, hS⟩ := hstrat
  obtain ⟨T, hT, hmodels⟩ := finite_stratification_models S
    (fun Y f ↦ HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M)) hS
  exact (constantModelConstructible_openImmersionLowerShriek
    ℓ p hpℓ k Λ j M T hT hmodels).1

/-- The finite native compact-support heart estimate when the chosen compactification is
scheme-theoretically dense.

(blueprint: lem-sf-finite-point-compact-heart-dense-bound)

Source: finite ordinary bound on the dense compactification
(blueprint: lem-sf-finite-point-finite-ordinary-bound, sk-lem-finite).

Proof: (1) since `c.i` is a dense open immersion, `topologicalKrullDim c.Z =
topologicalKrullDim X.left = d` (blueprint: lem-kun-dimension-extension). (2) The extension
by zero `M' = c.i_! M` is constant-model constructible on `c.Z`: a finite constant-model
stratification of `M` on `X.left` extends by the closed complement
(blueprint: lem-sf-open-extension-zero-constant-model-constructible). (3) The finite ordinary
bound gives `R(c.g)_* M'[0]` is `≤ 2d` (blueprint: lem-sf-finite-point-finite-ordinary-bound).
(4) The exact functor `c.i_!` commutes with the degree-zero single functor, so
`R(c.g)_* (c.i_! M[0]) ≅ R(c.g)_* M'[0]`, and the bound transports along this isomorphism.
-/
theorem finite_point_compact_heart_upper_bound_dense
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) (hn : 1 ≤ n)
    (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (hc : IsSchemeTheoreticallyDominant c.i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj
        (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left))
    (hM : IsConstantModelConstructible
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left M)
    (d : ℕ) (hd : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    ((rightDerivedLowerShriekOfCompactification
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * (d : ℤ)) := by
  let Λ := DerivedNakayama.quotientRing ℓ (ULift.{u} E) n
  let S := Spec (.of D.k)
  let : IsSchemeTheoreticallyDominant c.i := hc
  let : X.left.Over S := ⟨X.hom⟩
  let : LocallyOfFiniteType (X.left ↘ S) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  let : QuasiCompact (X.left ↘ S) := by
    change QuasiCompact X.hom
    infer_instance
  let : IsSeparated (X.left ↘ S) := by
    change IsSeparated X.hom
    infer_instance
  let : c.Z.Over S := ⟨c.g⟩
  let : LocallyOfFiniteType (c.Z ↘ S) := by
    change LocallyOfFiniteType c.g
    infer_instance
  let : QuasiCompact (c.Z ↘ S) := by
    change QuasiCompact c.g
    infer_instance
  let : IsSeparated (c.Z ↘ S) := by
    change IsSeparated c.g
    infer_instance
  let : c.i.IsOver S := ⟨by
    change c.i ≫ c.g = X.hom
    exact c.comm.symm⟩
  let : LocallyOfFiniteType (Over.mk c.g).hom := by
    change LocallyOfFiniteType c.g
    infer_instance
  let : QuasiCompact (Over.mk c.g).hom := by
    change QuasiCompact c.g
    infer_instance
  let : IsSeparated (Over.mk c.g).hom := by
    change IsSeparated c.g
    infer_instance
  let M' : Mod (Sheaf (Scheme.ProEt.topology c.Z) Ab.{u + 1})
      (condensedRingObj Λ c.Z) :=
    (CondensedRing.openImmersionLowerShriek Λ c.i).obj M
  have hM' : IsConstantModelConstructible Λ c.Z M' := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact open_extension_constructible ℓ D.p (Ne.symm hℓ) D.k Λ c.i M hM
  have hb := finite_point_finite_ordinary_bound ℓ E n hn (Over.mk c.g) M' hM' d (by
    let : c.Z.Over S := ⟨c.g⟩
    let : LocallyOfFiniteType (c.Z ↘ S) := by
      change LocallyOfFiniteType c.g
      infer_instance
    let : QuasiCompact (c.Z ↘ S) := by
      change QuasiCompact c.g
      infer_instance
    let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    let : IsDominant c.i := inferInstance
    have hdense : DenseRange c.i := c.i.denseRange
    have hdim : topologicalKrullDim c.Z = topologicalKrullDim X.left :=
      (topologicalKrullDim_fieldExtension_and_denseOpen (K := D.k) (X := c.Z)).2
        X.left c.i hdense |>.symm
    change topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)
    rw [hdim]
    exact hd.le)
  let F := CondensedRing.openImmersionLowerShriek Λ c.i
  let e := (R((c.g)_*⟦Λ⟧)).mapIso
    ((F.mapDerivedCategorySingleFunctor 0).app M)
  let K := (R((c.g)_*⟦Λ⟧)).obj
    ((DerivedCategory.singleFunctor _ 0).obj M')
  have hK : DerivedCategory.TStructure.t.IsLE K (2 * (d : ℤ)) := ⟨by
    simpa only [K, Λ, Over.mk_left, Over.mk_hom] using hb.le⟩
  have htransport :=
    (DerivedCategory.TStructure.t.le (2 * (d : ℤ))).prop_of_iso e.symm hK.le
  dsimp only [rightDerivedLowerShriekOfCompactification, Λ] at ⊢
  exact ⟨htransport⟩

end AlgebraicGeometry.ProEtale.CondensedRing
