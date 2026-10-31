/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerData

/-! # Canonical finite coefficient reduction data

Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md`, proof steps 1-2 (finite quotient reduction
and the specified comparison maps); setting of `sk-def-sf-setting`
(blueprint: def-sf-pf-finite-reduction-data).

The map and functors below are the canonical quotient reduction from
`A_{E,n+1}` to `A_{E,m+1}`. The six-functor comparison maps are the flatness-free
analogues of the published condensed coefficient-change maps of
`ChangeOfCoefficients`/`ChangeOfCoefficientsMate` (which assume flat scalar extension):
the Pull comparison is the scalar mate of `derivedComapLeftDerivedUpperStarIso`, the Push
comparison is the base-change mate of its inverse (as in `derivedPushHom_eq_mateEquiv`),
the compact-support comparison pastes Push with `derivedOpenImmersionShriekIso`, and the
tensor comparison is the tensorator of the left-derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor CategoryTheory.MonoidalCategory CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

instance quotientRing_isCommMonObj (n : ℕ) :
    IsCommMonObj (DerivedNakayama.quotientRing ell E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

instance quotientRing_monObj (n : ℕ) (X : Scheme.{u}) :
    MonObj (condensedRingObj (DerivedNakayama.quotientRing ell E n) X) :=
  ((upperStarFromPoint X).mapMon.obj
    (Mon.mk (DerivedNakayama.quotientRing ell E n))).mon

/-- The quotient map `A_{E,n+1} → A_{E,m+1}` for `m ≤ n`.
Source: blueprint `def-sf-pf-finite-reduction-data` (quotient reduction clause). -/
def quotientMap {m n : ℕ} (h : m ≤ n) :
    Padic.coefficientExtensionRing ell E (n + 1) →+*
      Padic.coefficientExtensionRing ell E (m + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The same quotient map on the continuous condensed coefficient rings.
Source: blueprint `def-sf-pf-finite-reduction-data` (condensed coefficient clause). -/
def ringMapSheaf {m n : ℕ} (h : m ≤ n) :
    DerivedNakayama.quotientRingSheaf ell E (n + 1) ⟶
      DerivedNakayama.quotientRingSheaf ell E (m + 1) := by
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  let q := quotientMap ell E h
  have hq : Continuous (q.comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E (n + 1)))) := by
    rw [show q.comp (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal ell E (n + 1))) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E (m + 1)) by
      exact Ideal.Quotient.factor_comp_mk
        (R := Padic.coefficientExtensionIntegers ell E)
        (S := Padic.coefficientExtensionIdeal ell E (n + 1))
        (T := Padic.coefficientExtensionIdeal ell E (m + 1))
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))]
    exact continuous_quot_mk
  have hq' : Continuous q :=
    (QuotientRing.isOpenQuotientMap_mk
      (Padic.coefficientExtensionIdeal ell E (n + 1))).continuous_comp_iff.mp hq
  let s : DerivedNakayama.quotientRingSheaf ell E (n + 1) ⟶
      DerivedNakayama.quotientRingSheaf ell E (m + 1) :=
    ⟨{
      app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((q.compLeftContinuous _ hq').comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩
  exact s

/-- The induced morphism of condensed coefficient rings.
Source: blueprint `def-sf-pf-finite-reduction-data` (coefficient-map clause). -/
def ringMap {m n : ℕ} (h : m ≤ n) :
    DerivedNakayama.quotientRing ell E (n + 1) ⟶
      DerivedNakayama.quotientRing ell E (m + 1) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (ringMapSheaf ell E h)

instance ringMap_isMonHom {m n : ℕ} (h : m ≤ n) :
    IsMonHom (ringMap ell E h) := by
  exact Sheaf.isMonHom_sheafCompose_map _ (ringMapSheaf ell E h)

/-- The canonical derived scalar-extension functor at a scheme.
Source: blueprint `def-sf-pf-finite-reduction-data`.
(blueprint: def-sf-pf-finite-reduction-data) -/
noncomputable def reduction {X : Scheme.{u}} {m n : ℕ} (h : m ≤ n) :
    CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) X ⥤
      CondensedRing.CompactificationReindexing.D
        (DerivedNakayama.quotientRing ell E (m + 1)) X :=
  let aX : condensedRingObj (DerivedNakayama.quotientRing ell E (n + 1)) X ⟶
      condensedRingObj (DerivedNakayama.quotientRing ell E (m + 1)) X :=
    AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) X
  (Mod.extendScalars aX).leftDerivedFunctor

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]

/-! The following maps are the flatness-free coefficient-change mates. -/

/-- The canonical Pull comparison `ρ_X ∘ Lg^*_n ⟶ Lg^*_m ∘ ρ_Y`, obtained as the scalar mate of
the restriction square `derivedComapLeftDerivedUpperStarIso` (Stacks 0D6D).
Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md` (comparison clause; blueprint:
def-sf-pf-finite-reduction-data). -/
noncomputable def derivedPullHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    L((g)^*⟦DerivedNakayama.quotientRing ell E (n + 1)⟧) ⋙
        L(Mod.extendScalars (coefficientMap (ringMap ell E h) X)) ⟶
      L(Mod.extendScalars (coefficientMap (ringMap ell E h) Y)) ⋙
        L((g)^*⟦DerivedNakayama.quotientRing ell E (m + 1)⟧) :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) X))).symm
      (derivedComapLeftDerivedUpperStarIso (ringMap ell E h) g).hom).natTrans

/-- The Pull mate is invertible, for every morphism `g` and on all unbounded objects.
Source: Stacks 0D6D (sites-cohomology, lemma-derived-pullback-composition), with Stacks 0G7E
and 07A4; recorded in node `def-sf-pf-finite-reduction-data`
(blueprint: def-sf-pf-finite-reduction-data).

Proof (postponed): (1) the change of coefficients `ρ` and the pullback `g` form a commuting
square of ringed topoi, the coefficient rings being pulled back from the point; (2) represent
an object by a K-flat complex `P` of flat terms; by Stacks 0G7E `g^*P` is again such, so
both sides are computed on `P` as `g^*P ⊗ Λ_m` and `g^*(P ⊗ Λ_m)`; (3) the mate of the restriction
square is the underived tensor comparison of `g^*` (Stacks 07A4) on these representatives,
which is an isomorphism; equivalently both composites are `L(ρ ∘ g)^*` (Stacks 0D6D). -/
theorem isIso_derivedPullHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) : IsIso (derivedPullHomFree ell E h g) := by
  sorry

/-- The canonical Push comparison `ρ_Y ∘ Rg_*^n ⟶ Rg_*^m ∘ ρ_X`, the base-change mate of the
inverse Pull comparison (Stacks 07A7).
Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md` (comparison clause; blueprint:
def-sf-pf-finite-reduction-data). -/
noncomputable def derivedPushHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    R((g)_*⟦DerivedNakayama.quotientRing ell E (n + 1)⟧) ⋙
        L(Mod.extendScalars (coefficientMap (ringMap ell E h) Y)) ⟶
      L(Mod.extendScalars (coefficientMap (ringMap ell E h) X)) ⋙
        R((g)_*⟦DerivedNakayama.quotientRing ell E (m + 1)⟧) := by
  letI := isIso_derivedPullHomFree ell E h g
  exact (mateEquiv
    (derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.quotientRing ell E (n + 1)) g)
    (derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.quotientRing ell E (m + 1)) g)
    (TwoSquare.mk _ _ _ _ (inv (derivedPullHomFree ell E h g)))).natTrans

/-- The canonical Shriek mate for a chosen compactification, without flatness: Push for the
proper part followed by the open extension-by-zero isomorphism.
Source: Stacks 0GL6, 07A7 (blueprint: def-sf-pf-finite-reduction-data). -/
noncomputable def derivedLowerShriekHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] :
    R(f)_!⟦DerivedNakayama.quotientRing ell E (n + 1)⟧ ⋙
        L(Mod.extendScalars (coefficientMap (ringMap ell E h) Y)) ⟶
      L(Mod.extendScalars (coefficientMap (ringMap ell E h) X)) ⋙
        R(f)_!⟦DerivedNakayama.quotientRing ell E (m + 1)⟧ := by
  let c := HasCompactification.compactification f
  exact (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open⟦DerivedNakayama.quotientRing ell E (n + 1)⟧)
      (derivedPushHomFree ell E h c.g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso (ringMap ell E h) c.i).hom
      R((c.g)_*⟦DerivedNakayama.quotientRing ell E (m + 1)⟧)

/-- The compact-support coefficient comparison, defined by the canonical Shriek mate.
Source: Stacks 0GL6 (blueprint: def-sf-pf-finite-reduction-data). -/
noncomputable def c_f {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
    {m n : ℕ} (h : m ≤ n)
    (K : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) X) :
    (reduction ell E h).obj
        ((CondensedRing.CompactificationReindexing.F
          (DerivedNakayama.quotientRing ell E (n + 1))
          (HasCompactification.compactification f)).obj K) ⟶
      (CondensedRing.CompactificationReindexing.F
        (DerivedNakayama.quotientRing ell E (m + 1))
        (HasCompactification.compactification f)).obj
        ((reduction ell E h).obj K) :=
  (derivedLowerShriekHomFree ell E h (f := f)).app K

/-- The tensor comparison from the strong monoidal derived scalar extension.
Source: Stacks 07A4 (blueprint: def-sf-pf-finite-reduction-data). -/
noncomputable def s {T : Scheme.{u}} {m n : ℕ} (h : m ≤ n)
    (K L : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) T) :
    (reduction ell E h).obj (K ⊗ L) ⟶
    (reduction ell E h).obj K ⊗ (reduction ell E h).obj L := by
  letI := Mod.extendScalarsMonoidal
      (AlgebraicGeometry.ProEtale.coefficientMap (ringMap ell E h) T)
  letI : (reduction ell E h).Monoidal :=
    (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap
      (ringMap ell E h) T)).leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.μIso (reduction ell E h) K L).inv

/-- The Pull comparison, the mate of the flatness-free derived restriction square.
Source: Stacks 0D6D (blueprint: def-sf-pf-finite-reduction-data). -/
noncomputable def t {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
    {m n : ℕ} (h : m ≤ n)
    (L : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) Y) :
    (reduction ell E h).obj ((CondensedRing.CompactificationReindexing.P
      (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L) ⟶
      (CondensedRing.CompactificationReindexing.P
        (DerivedNakayama.quotientRing ell E (m + 1)) f).obj
        ((reduction ell E h).obj L) :=
  (derivedPullHomFree ell E h f).app L

/-- The induced tensor-pullback comparison `a^f = (1 ⊗ t) s`.
Source: blueprint `def-sf-pf-finite-reduction-data` (comparison clause). -/
noncomputable def a_f {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
    {m n : ℕ} (h : m ≤ n)
    (K : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) X)
    (L : CondensedRing.CompactificationReindexing.D
      (DerivedNakayama.quotientRing ell E (n + 1)) Y) :
    (reduction ell E h).obj (K ⊗
      (CondensedRing.CompactificationReindexing.P
        (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L) ⟶
      (reduction ell E h).obj K ⊗
        (CondensedRing.CompactificationReindexing.P
          (DerivedNakayama.quotientRing ell E (m + 1)) f).obj
          ((reduction ell E h).obj L) :=
  s ell E h K ((CondensedRing.CompactificationReindexing.P
    (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L) ≫
    (𝟙 _ ⊗ₘ t ell E h L)

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction
