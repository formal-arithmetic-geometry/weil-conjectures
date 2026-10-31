/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
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
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Finite-stage hypotheses for ordinary exceptional comparison

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
thm-pur-cohomological-smoothness.proof.md, first paragraph, finite coefficient stage
(blueprint: lem-pur-finite-setting-comparison-hypotheses).

The ring is the recorded quotient O_E/(varpi_E^n). The annihilator here is ell^n,
which works at every positive level, including ramified coefficient extensions.
Compactifications and chosen Cartesian squares are the existing constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem finite_type_geometry {K : Type u} [Field K] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of K)) (aY : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X ∧ CompactSpace X ∧ QuasiSeparatedSpace X ∧
    IsNoetherian Y ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
    (∃ c : Compactification f, QuasiCompact c.i) ∧
    (∀ c : Compactification f,
      QuasiCompact c.i ∧
      LocallyOfFiniteType (c.g ≫ aY) ∧ QuasiCompact (c.g ≫ aY) ∧
      IsNoetherian c.Z ∧
      ∃ D : ℕ, topologicalKrullDim c.Z ≤ (D : WithBot ℕ∞)) := by
  let := LocallyOfFiniteType.isLocallyNoetherian aX
  let := QuasiCompact.compactSpace_of_compactSpace aX
  let : IsNoetherian X := {}
  let := LocallyOfFiniteType.isLocallyNoetherian aY
  let := QuasiCompact.compactSpace_of_compactSpace aY
  let : IsNoetherian Y := {}
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨NagataCompactification f, ?_⟩, ?_⟩
  · exact (NagataCompactification f).quasiCompact_openImmersion inferInstance
  · intro c
    let := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY)
    let := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aY)
    let : IsNoetherian c.Z := {}
    exact ⟨c.quasiCompact_openImmersion inferInstance, inferInstance, inferInstance,
      inferInstance, exists_topologicalKrullDim_le (c.g ≫ aY)⟩

private theorem coefficient_power_zero (P : PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ P.level : ℕ) : P.Ring) = 0 := by
  let l := P.coefficients.l
  let E := P.extension
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (hdvr.2.1 _).2
    change spectralNorm (Padic l) E (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E),
      spectralNorm_extends (K := Padic l) (L := E)]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change ((l ^ P.level : ℕ) :
    Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E P.level) = 0
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  change (l : Padic.coefficientExtensionIntegers l E) ^ P.level ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ P.level
  rw [hgen]
  exact Ideal.pow_mem_pow hm P.level

/-- Finite-stage geometric and coefficient hypotheses for ordinary exceptional comparison.
No separatedness of either structure morphism is assumed. For a compactification `c`,
its structure map over k is `c.g ≫ aY`; no independent structure is chosen on `c.Z`.
The dimension bound is a natural number, so zero is permitted even for the empty scheme.
The same conclusions are asserted for every chosen Cartesian base change to a finite-type
k-scheme. In particular they apply when `f` is smooth of any pure relative dimension,
including zero, supplying the ordinary smooth tensor and bounded-below exceptional Hom
comparison hypotheses without asserting a new comparison of functors.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
thm-pur-cohomological-smoothness.proof.md, first paragraph, finite coefficient stage
(blueprint: lem-pur-finite-setting-comparison-hypotheses).

Proof:
1. Spec k is Noetherian since k is a field. Apply
   [lem-weil-pbc-finite-type-over-noetherian] to aX and aY to obtain Noetherianity
   and quasi-compactness of X and Y. Apply
   [lem-weil-pbc-locally-noetherian-quasi-separated] for quasi-separatedness.
2. Apply [thm-nagata-compactification] to the separated finite-type f over the qcqs Y.
   For every compactification c, properness of c.g includes finite type by
   [def-weil-proper-morphism]. Composition with aY is finite type by
   [lem-sfb-finite-type-composition-base-change]. The same Noetherianity argument applies
   to c.Z. By [lem-weil-pbc-qcqs-morphism-permanence], c.i is quasi-compact.
3. Apply [lem-kun-dimension-finite-type] to c.g followed by aY. The dimension in
   [def-kun-dimension] and [def-kun-topological-krull-dimension] is the same supremum
   over strict chains of nonempty irreducible closed subsets. Choose a natural bound D;
   if c.Z is empty its dimension is bottom, and D=0 suffices.
4. By [lem-weil-l-adic-extension-absolute-value] and
   [lem-weil-l-adic-extension-integers-dvr], O_E is a DVR with finite residue field and
   ell in its maximal ideal (varpi_E). Apply [lem-weil-valued-dvr-finite-quotients]
   for finiteness. Write ell=varpi_E*b, using |ell|=ell^(-1)<1 from
   [def-weil-l-adic-numbers]. Raising to n gives ell^n=varpi_E^n*b^n, whose image in
   A is zero and thus annihilates every element. No unramifiedness is used.
5. The integer N=ell^n is positive. Since ell differs from the characteristic p,
   its image and that of N are units in k. Every structure map from a k-scheme
   preserves those units in global sections, including for the empty scheme.
6. For any chosen Cartesian square over a finite-type Y',
   [lem-pod-separated-finite-type-base-change] gives separatedness and finite type
   of f'. Composition makes X' finite type over k. Repeat Steps 1--3 for f';
   Steps 4--5 use the same coefficient ring and N. The smooth specialization only
   checks the stated hypotheses and makes no further functorial assertion. -/
theorem finite_setting_comparison_hypotheses (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of P.field.k))
    (aY : Y ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X ∧ CompactSpace X ∧ QuasiSeparatedSpace X ∧
    IsNoetherian Y ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
    (∃ c : Compactification f, QuasiCompact c.i) ∧
    (∀ c : Compactification f,
      QuasiCompact c.i ∧
      LocallyOfFiniteType (c.g ≫ aY) ∧ QuasiCompact (c.g ≫ aY) ∧
      IsNoetherian c.Z ∧
      ∃ D : ℕ, topologicalKrullDim c.Z ≤ (D : WithBot ℕ∞)) ∧
    Finite P.Ring ∧ 1 ≤ P.coefficients.l ^ P.level ∧
    (∀ a : P.Ring, (P.coefficients.l ^ P.level) • a = 0) ∧
    (∀ (T : Scheme.{u}) (_aT : T ⟶ Spec (CommRingCat.of P.field.k)),
      IsUnit ((P.coefficients.l ^ P.level : ℕ) : Γ(T, ⊤))) ∧
    (∀ (X' Y' : Scheme.{u})
      (aY' : Y' ⟶ Spec (CommRingCat.of P.field.k))
      [LocallyOfFiniteType aY'] [QuasiCompact aY']
      (g : Y' ⟶ Y) (_hg : g ≫ aY = aY')
      (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (_sq : ChosenCartesianSquare g' f' f g),
      IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧
      LocallyOfFiniteType (f' ≫ aY') ∧ QuasiCompact (f' ≫ aY') ∧
      IsNoetherian X' ∧ CompactSpace X' ∧ QuasiSeparatedSpace X' ∧
      IsNoetherian Y' ∧ CompactSpace Y' ∧ QuasiSeparatedSpace Y' ∧
      (∃ c : Compactification f', QuasiCompact c.i) ∧
      (∀ c : Compactification f',
        QuasiCompact c.i ∧
        LocallyOfFiniteType (c.g ≫ aY') ∧ QuasiCompact (c.g ≫ aY') ∧
        IsNoetherian c.Z ∧
        ∃ D : ℕ, topologicalKrullDim c.Z ≤ (D : WithBot ℕ∞))) := by
  obtain ⟨hX, hXc, hXs, hY, hYc, hYs, hc, hall⟩ := finite_type_geometry aX aY f
  refine ⟨hX, hXc, hXs, hY, hYc, hYs, hc, hall,
    Padic.finite_coefficientExtensionRing _ _ _ P.level_pos,
    one_le_pow₀ (Fact.out : P.coefficients.l.Prime).one_le, ?_, ?_, ?_⟩
  · intro a
    rw [nsmul_eq_mul, coefficient_power_zero P, zero_mul]
  · intro T aT
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    change IsUnit ((T.toRingedSpace.presheaf.germ ⊤ t ht).hom
      ((P.coefficients.l ^ P.level : ℕ) : Γ(T, ⊤)))
    rw [map_natCast, Nat.cast_pow]
    exact (P.coefficientPrime_isUnit_stalk T aT t).pow P.level
  · intro X' Y' aY' _ _ g _hg g' f' sq
    have hs : IsSeparated f' := by
      rw [← sq.hom_snd]
      infer_instance
    have hl : LocallyOfFiniteType f' := by
      rw [← sq.hom_snd]
      infer_instance
    have hq : QuasiCompact f' := by
      rw [← sq.hom_snd]
      infer_instance
    let := hs
    let := hl
    let := hq
    exact ⟨hs, hl, hq, inferInstance, inferInstance,
      finite_type_geometry (f' ≫ aY') aY' f'⟩

end WeilConjectures.PurityFiniteSetting
