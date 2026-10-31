/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ScalarSixCompactSupport
import all WeilConjectures.AlgebraicGeometry.CoefficientProjectionSquare
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.SixFunctors.ListedCoefficientCtf

/-! The two compact-support coefficient comparisons in the finite reduction square.

The source is the compact-support comparison step of
`det-prop-sf-pf-reduction` (blueprint: det-prop-sf-pf-reduction).  The proof is
deferred because it requires transporting the ordinary-etale universal tensor
presentation through the native condensed compactification functor; the two
components are the exact vertical arrows needed by the reduction square.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Functor
noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finiteCoefficientListed
    (ell : ℕ) [Fact ell.Prime]
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
    (φ : A →+* B)
    (a : (⟨Profinite.continuousCoefficientRingObj A⟩ : ScalarSixRing.{u}) ⟶
      ⟨Profinite.continuousCoefficientRingObj B⟩)
    (ha : ∀ (S : Profinite.{u})
      (s : (Profinite.continuousCoefficientRingObj A).obj.obj (Opposite.op S)) (x : S),
      ((a.hom.hom.hom.app (Opposite.op S)) s).down x = φ (s.down x)) :
    ListedCoefficientMap ell a := by
  cases DiscreteTopology.eq_bot (α := A)
  cases DiscreteTopology.eq_bot (α := B)
  exact .finite A B hA hB φ a ha

private def finiteReductionScalarMap
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (h : m ≤ n) :
    (⟨DerivedNakayama.quotientRing ell E (n + 1)⟩ : ScalarSixRing.{u}) ⟶
      ⟨DerivedNakayama.quotientRing ell E (m + 1)⟩ :=
  ⟨⟨FiniteReduction.ringMap ell E h⟩⟩

private theorem finiteReduction_annihilator
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    ∃ a : ℕ, ∀ x : Padic.coefficientExtensionRing ell E (n + 1), (ell ^ a) • x = 0 := by
  let R := Padic.coefficientExtensionIntegers ell E
  let J := Padic.coefficientExtensionMaximalIdeal ell E
  have h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) = J :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hell : (ell : R) ∈ J := by
    apply (h.2.1 _).mpr
    change spectralNorm ℚ_[ell] E (ell : E) < 1
    rw [← map_natCast (algebraMap ℚ_[ell] E) ell, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hz : (ell : Padic.coefficientExtensionRing ell E (n + 1)) ^ (n + 1) = 0 := by
    have hm : (ell : R) ^ (n + 1) ∈ Padic.coefficientExtensionIdeal ell E (n + 1) := by
      change (ell : R) ^ (n + 1) ∈
        Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) ^ (n + 1)
      rw [hgen]
      exact Ideal.pow_mem_pow hell _
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  exact ⟨n + 1, fun x ↦ by simp only [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]⟩

private theorem finiteReduction_listed
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (h : m ≤ n) :
    ListedCoefficientMap ell (finiteReductionScalarMap ell E h) := by
  let := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  let := DerivedNakayama.quotientDiscrete ell E (n + 1)
  let := DerivedNakayama.quotientDiscrete ell E (m + 1)
  let := Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos _)
  let := Padic.finite_coefficientExtensionRing ell E (m + 1) (Nat.succ_pos _)
  exact finiteCoefficientListed ell _ _ (finiteReduction_annihilator ell E n)
    (finiteReduction_annihilator ell E m) (FiniteReduction.quotientMap ell E h)
    (finiteReductionScalarMap ell E h) (by intros; rfl)

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem finiteReduction_mate_ofNatIsoLeft
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R : B ⥤ A} {M M' : C ⥤ D} {S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (e : L ≅ L') (d : M ≅ M')
    {G : A ⥤ C} {H : B ⥤ D} (α : TwoSquare G L M H) :
    (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft d)
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft G d.inv ≫ α.natTrans ≫ Functor.whiskerRight e.hom H))).natTrans =
      (mateEquiv a b α).natTrans := by
  ext K
  simp [mateEquiv, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    ← Functor.map_comp, Category.assoc]

set_option maxHeartbeats 2000000 in
-- The scalar-adjunction mates commute with the exact-left-derived coordinate changes.
private theorem finiteReduction_pull_eq
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPullHom (finiteReductionScalarMap ell E h) f =
      Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing ell E (n + 1)) f).inv
          (scalarSixChange (finiteReductionScalarMap ell E h) X) ≫
        FiniteReduction.derivedPullHomFree ell E h f ≫
        Functor.whiskerLeft (scalarSixChange (finiteReductionScalarMap ell E h) Y)
          (leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing ell E (m + 1)) f).hom := by
  let A := DerivedNakayama.quotientRing ell E (n + 1)
  let B := DerivedNakayama.quotientRing ell E (m + 1)
  let a := FiniteReduction.ringMap ell E h
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv adjY adjX).injective
  change mateEquiv adjY adjX ((mateEquiv adjY adjX).symm
      (.mk _ _ _ _ (derivedComapUpperStarIso a f).inv)) = _
  rw [Equiv.apply_symm_apply]
  have ht := mateEquiv_whiskerTop_whiskerBottom adjY adjX
    (.mk _ _ _ _ (FiniteReduction.derivedPullHomFree ell E h f))
    (leftDerivedUpperStarIsoMapDerivedCategory A f).inv
    (leftDerivedUpperStarIsoMapDerivedCategory B f).hom
  have hb : mateEquiv adjY adjX
      (.mk _ _ _ _ (FiniteReduction.derivedPullHomFree ell E h f)) =
      .mk _ _ _ _ (derivedComapLeftDerivedUpperStarIso a f).hom := by
    exact (mateEquiv adjY adjX).apply_symm_apply _
  have hm := congrArg (fun (t : TwoSquare _ _ _ _) ↦
      (t.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A f).inv).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).hom) hb
  refine Eq.trans ?_ (Eq.trans (ht.trans hm).symm ?_)
  · ext K
    simp only [A, B, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
      derivedComapLeftDerivedUpperStarIso, derivedComapUpperStarIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    have hi := (Mod.comap (coefficientMap a X)).mapDerivedCategory.map_id
      ((upperStar B f).mapDerivedCategory.obj K)
    let p := ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryCompIso
      (upperStar A f)).inv.app K
    let q := (Functor.mapDerivedCategoryNatIso (comapUpperStarIso a f)).inv.app K
    let r := ((upperStar B f).mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap a X))).hom.app K
    simpa only [A, B, Category.assoc] using
      (Category.comp_id (p ≫ q ≫ r)).symm.trans
        (congrArg (fun t ↦ (p ≫ q ≫ r) ≫ t) hi.symm)
  · apply congrArg (mateEquiv adjY adjX)
    ext K
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.equivNatTrans,
      TwoSquare.mk, scalarSixChange, scalarSixAdjunctionLeft, A, B, a,
      finiteReductionScalarMap]

set_option maxHeartbeats 2000000 in
-- The geometric mate respects the same coordinate changes and specified adjunctions.
private theorem finiteReduction_push_eq
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarDirectImageMate (finiteReductionScalarMap ell E h) f =
      FiniteReduction.derivedPushHomFree ell E h f := by
  let A := DerivedNakayama.quotientRing ell E (n + 1)
  let B := DerivedNakayama.quotientRing ell E (m + 1)
  let a := finiteReductionScalarMap ell E h
  let := FiniteReduction.isIso_derivedPullHomFree ell E h f
  have htheta : scalarDirectImagePullbackData.theta a f =
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A f).symm
        (scalarSixChange a X) ≪≫ asIso (FiniteReduction.derivedPullHomFree ell E h f) ≪≫
        Functor.isoWhiskerLeft (scalarSixChange a Y)
          (leftDerivedUpperStarIsoMapDerivedCategory B f) := by
    apply Iso.ext
    exact (scalarDirectImagePullbackData.thetaNormalization a f).trans
      (finiteReduction_pull_eq ell E h f)
  change scalarDirectImageMate a f = _
  unfold scalarDirectImageMate
  rw [htheta]
  have ht := finiteReduction_mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction A f) (derivedUpperStarLowerStarAdjunction B f)
    (leftDerivedUpperStarIsoMapDerivedCategory A f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (.mk _ _ _ _ (inv (FiniteReduction.derivedPullHomFree ell E h f)))
  simpa only [RootCoordinateFace.adjunction, RootCoordinateFace.upper,
    RootCoordinateFace.lower, moduleObjectDerivedPushforward, Adjunction.mapDerived_eq,
    scalarSixChange, scalarSixAdjunctionLeft, TwoSquare.mk, TwoSquare.equivNatTrans,
    derivedUpperStarLowerStarAdjunction, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, asIso_inv, Category.assoc, FiniteReduction.derivedPushHomFree,
    A, B, a, finiteReductionScalarMap, id_eq, TwoSquare.natTrans] using ht

set_option maxHeartbeats 2000000 in
-- Assemble the two comparisons while keeping the derived functor models folded.
/-- The compact-support coefficient comparisons `c_f(K)` and `c_f(K ⊗ Lf^*L)` of the finite
reduction square are isomorphisms.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
det-prop-sf-pf-reduction.proof.md`, step 3 ("Both horizontal maps are isomorphisms at the finite
levels"), node `det-prop-sf-pf-reduction`.

Proof: (1) by [lem-sf-pf-reduction-witnessed-flat-domains], `K` and `H = K ⊗ Lf^*L` have bounded
flat constructible etale witnesses, and so do `j_!K`, `j_!H` for the chosen compactification
`X →j Z →r Y` of [det-def-sf-exchanges]; (2) by construction `c_f(V) = Rr_{*}(d_V) ∘ c_{j_!V}`
with `d_V` the open extension-by-zero comparison, an isomorphism
([lem-sf-pf-reduction-proper-open-identities]); (3) the proper comparison `c_{j_!V}` is the
compact-support coefficient change of [lem-fix-compact-support-coefficient-change], an
isomorphism on bounded constructible finite-Tor complexes; hence both `c_f(K)` and `c_f(H)` are
isomorphisms. (blueprint: det-prop-sf-pf-reduction-compact-support-iso) -/
theorem finiteReduction_compactSupport_isIso
    (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (hmn : m ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] {f : X ⟶ Y}
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (K : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) X)
    (L : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) Y) :
    IsIso (FiniteReduction.c_f (f := f) ell E hmn K.obj) ∧
      IsIso (FiniteReduction.c_f (f := f) ell E hmn
        (K.obj ⊗ (CompactificationReindexing.P
          (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L.obj)) := by
  classical
  let := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  have : Fact (ringChar D.k ≠ ell) := ⟨by rw [ringChar.eq D.k D.p]; exact hEll.symm⟩
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let a := finiteReductionScalarMap ell E hmn
  have ha := finiteReduction_listed ell E hmn
  have hcd := BaseFieldFiniteCD.of_isAlgClosed ell D.k
  have hA := (listedCoefficientCtf ell a ha).1
  have hs := constructibleFiniteTor_stability_direct_images ell D.k hcd
    (DerivedNakayama.quotientRing ell E (n + 1)) hA f
  have hp := hs.1 L.obj L.property
  have hH := hs.2.1 K.obj _ K.property hp
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  have : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  have : IsSeparated (Over.mk (X ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of D.k)))
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
  have : IsSeparated (Over.mk (Y ↘ Spec (.of D.k))).hom :=
    inferInstanceAs (IsSeparated (Y ↘ Spec (.of D.k)))
  let f₀ : Over.mk (X ↘ Spec (.of D.k)) ⟶ Over.mk (Y ↘ Spec (.of D.k)) :=
    Over.homMk f (comp_over f (Spec (.of D.k)))
  have hc (V : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) X) :
      IsIso (FiniteReduction.c_f (f := f) ell E hmn V.obj) := by
    have hi := ((scalarSixCompactSupport ell D.k hcd a ha f₀).1
      (HasCompactification.compactification f) V).1
    simp only [scalarCompactSupportMap, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id] at hi
    change IsIso ((scalarDirectImageMate (finiteReductionScalarMap ell E hmn)
      (HasCompactification.compactification f).g).app _ ≫ _) at hi
    rw [finiteReduction_push_eq] at hi
    simp only [FiniteReduction.c_f, FiniteReduction.derivedLowerShriekHomFree,
      Functor.comp_obj,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp]
    erw [Category.id_comp]
    exact hi
  exact ⟨hc K, hc ⟨_, hH⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
