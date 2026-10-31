/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement

import WeilConjectures.AlgebraicGeometry.FiniteCoefficientProperFormulaTools
import WeilConjectures.AlgebraicGeometry.OpenExtensionConstructibleFiniteTor
import WeilConjectures.SixFunctors.ListedCoefficientCtf
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

/-! The endpoint isomorphism equivalence for the finite reduction square.

This is step 3 of `det-prop-sf-pf-reduction` (blueprint:
det-prop-sf-pf-reduction). Both native endpoint maps are invertible: factor through
the finite proper projection formula and the open projection isomorphism.
Listed coefficient preservation supplies the domain at the reduced level.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Functor
noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finite_compact_projection_isIso
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ r : ℕ, (ell ^ r : ℕ) • (1 : A) = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousCoefficientRingObj A) X)
    (L : ConstantModelConstructibleFiniteTor (Profinite.continuousCoefficientRingObj A) Y) :
    IsIso (CompactificationReindexing.pf (Profinite.continuousCoefficientRingObj A)
      c K.obj L.obj) := by
  let R := Profinite.continuousCoefficientRingObj A
  let U : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  have : LocallyOfFiniteType U.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  have : QuasiCompact U.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  have : IsSeparated U.hom := ‹IsSeparated (X ↘ Spec (.of k))›
  let Z : Over (Spec (.of k)) := Over.mk (c.g ≫ (Y ↘ Spec (.of k)))
  have : LocallyOfFiniteType Z.hom := inferInstanceAs
    (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact Z.hom := inferInstanceAs
    (QuasiCompact (c.g ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated Z.hom := inferInstanceAs
    (IsSeparated (c.g ≫ (Y ↘ Spec (.of k))))
  let j : U ⟶ Z := Over.homMk c.i (by
    change c.i ≫ c.g ≫ (Y ↘ Spec (.of k)) = (X ↘ Spec (.of k))
    rw [← Category.assoc, ← c.comm, comp_over f (Spec (.of k))])
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion c.i)
  obtain ⟨a, b, hcoh⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K.obj).mpr K.property.1.1
  obtain ⟨d, e, htor⟩ := K.property.2
  have hJ := (openExtension_constructible_finiteTor ell k R j K
    a b d e hcoh htor).1
  let : c.Z.Over (Spec (.of k)) := ⟨Z.hom⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := ‹LocallyOfFiniteType Z.hom›
  have : QuasiCompact (c.Z ↘ Spec (.of k)) := ‹QuasiCompact Z.hom›
  have : IsSeparated (c.Z ↘ Spec (.of k)) := ‹IsSeparated Z.hom›
  have : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hP := (finiteCoefficientProperFormulas R A (Iso.refl _) ell hA k c.g).2
    ((CompactificationReindexing.J R c.i).obj K.obj) L.obj hJ L.property
  have : IsIso (moduleObjectProjectionMap R c.g
      ((CompactificationReindexing.J R c.i).obj K.obj) L.obj) := hP
  rw [CompactificationReindexing.pf_factorization]
  infer_instance

private theorem discrete_scalar_ctf
    (ell : ℕ) [Fact ell.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    [tA : TopologicalSpace A] [tB : TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] [IsTopologicalRing A] [IsTopologicalRing B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
    (φ : A →+* B)
    (a : (⟨Profinite.continuousCoefficientRingObj A⟩ : ScalarSixRing.{u}) ⟶
      ⟨Profinite.continuousCoefficientRingObj B⟩)
    (ha : ∀ (P : Profinite.{u})
      (s : (Profinite.continuousCoefficientRingObj A).obj.obj (.op P)) (x : P),
      ((a.hom.hom.hom.app (.op P)) s).down x = φ (s.down x))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousCoefficientRingObj A)
      X.left) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj B) X.left
        ((scalarSixChange a X.left).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K.obj) := by
  have htA : tA = ⊥ := DiscreteTopology.eq_bot (α := A)
  have htB : tB = ⊥ := DiscreteTopology.eq_bot (α := B)
  subst tA
  subst tB
  exact (listedCoefficientCtf ell a
    (ListedCoefficientMap.finite A B hA hB φ a ha)).2.2 k X K.obj K.property

private theorem quotient_torsion
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    ∃ r : ℕ, ∀ x : Padic.coefficientExtensionRing ell E (n + 1),
      (ell ^ r) • x = 0 := by
  have h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
      Set (Padic.coefficientExtensionIntegers ell E)) =
        Padic.coefficientExtensionMaximalIdeal ell E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hl : (ell : Padic.coefficientExtensionIntegers ell E) ∈
      Padic.coefficientExtensionMaximalIdeal ell E := by
    apply h.2.1 _ |>.mpr
    change spectralNorm ℚ_[ell] E (ell : E) < 1
    rw [← map_natCast (algebraMap ℚ_[ell] E) ell, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hz : ((ell : Padic.coefficientExtensionRing ell E (n + 1)) ^ (n + 1)) = 0 := by
    have hm : (ell : Padic.coefficientExtensionIntegers ell E) ^ (n + 1) ∈
        Padic.coefficientExtensionIdeal ell E (n + 1) := by
      unfold Padic.coefficientExtensionIdeal
      rw [hgen]
      exact Ideal.pow_mem_pow hl _
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  refine ⟨n + 1, fun x ↦ ?_⟩
  rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]

/-- The native projection maps at the two finite levels are isomorphisms simultaneously.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
det-prop-sf-pf-reduction.proof.md`, step 3 ("Both horizontal maps are isomorphisms at the finite
levels"), node `det-prop-sf-pf-reduction`.

Proof: the actual quotient topology is discrete and the coefficient prime is nilpotent
in every positive quotient. Exact open extension preserves bounded constant-model
constructibility and finite Tor amplitude. The finite proper projection theorem therefore
makes the proper factor invertible; the native proper/open factorization expresses `pf`
as that factor followed by isomorphisms. The specified quotient map is a listed finite
coefficient map, so its derived scalar extension preserves the same constructible finite-Tor
domain. Applying the factorization argument at both levels proves both propositions;
`iff_of_true` gives their equivalence. No flatness of the quotient map is assumed.
(blueprint: det-prop-sf-pf-reduction-iso-iff) -/
theorem finiteReduction_projection_isIso_iff
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
      (IsIso (CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (n + 1))
          (HasCompactification.compactification f) K.obj L.obj) ↔
        IsIso (CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)
          ((FiniteReduction.reduction ell E hmn).obj K.obj)
          ((FiniteReduction.reduction ell E hmn).obj L.obj))) := by
  let := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  let := DerivedNakayama.quotientDiscrete ell E (n + 1)
  let := DerivedNakayama.quotientDiscrete ell E (m + 1)
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  let a : (⟨DerivedNakayama.quotientRing ell E (n + 1)⟩ : ScalarSixRing.{u}) ⟶
      ⟨DerivedNakayama.quotientRing ell E (m + 1)⟩ :=
    ⟨⟨FiniteReduction.ringMap ell E hmn⟩⟩
  have reduced {T : Scheme.{u}} [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
      [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]
      (M : ConstantModelConstructibleFiniteTor
        (DerivedNakayama.quotientRing ell E (n + 1)) T) :
      (constantModelBoundedConstructible (DerivedNakayama.quotientRing ell E (m + 1)) T ⊓
        DerivedCategory.finiteTorAmplitude _)
        ((FiniteReduction.reduction ell E hmn).obj M.obj) := by
    let S : Over (Spec (.of D.k)) := Over.mk (T ↘ Spec (.of D.k))
    have : LocallyOfFiniteType S.hom := ‹LocallyOfFiniteType (T ↘ Spec (.of D.k))›
    have : QuasiCompact S.hom := ‹QuasiCompact (T ↘ Spec (.of D.k))›
    have : IsSeparated S.hom := ‹IsSeparated (T ↘ Spec (.of D.k))›
    exact discrete_scalar_ctf ell
      (Padic.coefficientExtensionRing ell E (n + 1))
      (Padic.coefficientExtensionRing ell E (m + 1))
      (quotient_torsion ell E n) (quotient_torsion ell E m)
      (FiniteReduction.quotientMap ell E hmn) a (fun _ _ _ ↦ rfl)
      D.k S M
  exact iff_of_true
    (finite_compact_projection_isIso ell D.k
      (Padic.coefficientExtensionRing ell E (n + 1))
      (by obtain ⟨r, hr⟩ := quotient_torsion ell E n; exact ⟨r, hr 1⟩)
      (HasCompactification.compactification f) K L)
    (finite_compact_projection_isIso ell D.k
      (Padic.coefficientExtensionRing ell E (m + 1))
      (by obtain ⟨r, hr⟩ := quotient_torsion ell E m; exact ⟨r, hr 1⟩)
      (HasCompactification.compactification f)
      ⟨_, reduced K⟩ ⟨_, reduced L⟩)

end AlgebraicGeometry.ProEtale.CondensedRing
