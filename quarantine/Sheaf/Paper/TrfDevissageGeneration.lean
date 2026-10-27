/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.FlatModel
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Generators

import Sheaf.CategoryTheory.NilpotentFiberHomology
import Sheaf.Paper.TrfKummerMonodromy
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Constructible devissage and the need for lisse coefficients

Source: Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation/`
`lem-trf-devissage-generation.md`, statement and Steps 0--3
(blueprint: lem-trf-devissage-generation).

The lisse-flat generator family is the published `sfProEtaleClosureGenerators`.
Closed direct image is exact, so its sheaf-level formula in degree zero represents
`Rg_*j_!L`. The second clause of the statement is an existential obstruction to replacing
all such L by the constant rank-one coefficient sheaf; it is not a claim for every X.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem trf_coefficient_primary
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 0 < r ∧ (l ^ r) • (1 : Padic.coefficientExtensionRing l E n) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hnorm : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have he := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
    change Padic.coefficientExtensionAbsoluteValue l E
      (algebraMap (Padic l) E (l : Padic l)) = _ at he
    simpa only [map_natCast] using he.trans_lt (Padic.norm_p_lt_one (p := l))
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := (h.2.1 _).2 hnorm
  have hp : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    unfold Padic.coefficientExtensionIdeal
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  have hz : (l : Padic.coefficientExtensionRing l E n) ^ n = 0 := by
    simpa only [map_pow, map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  exact ⟨n, hn, by simpa only [nsmul_eq_mul, Nat.cast_pow, mul_one] using hz⟩

private theorem trf_finite_support_iff (P : ℤ → Prop) :
    Set.Finite {q | ¬ P q} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → P q := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    by_contra hn
    rcases hq with hq | hq
    · exact (not_lt_of_ge (ha hn)) (hq.trans_le (min_le_left a b))
    · exact (not_lt_of_ge (hb hn)) ((le_max_right a b).trans_lt hq)
  · rintro ⟨a, b, -, h⟩
    apply (Set.finite_Icc a b).subset
    intro q hq
    exact ⟨le_of_not_gt (fun hqa ↦ hq (h q (.inl hqa))),
      le_of_not_gt (fun hbq ↦ hq (h q (.inr hbq)))⟩


/-- The constant-coefficient subfamily in the final sentence of the statement.
The actual stratum immersion factors through its scheme-theoretic closure, and the
coefficient sheaf is the sheafification of the constant regular module A. The canonical
intrinsic realization retains its scalar action. Closed direct image is exact, so this
sheaf in degree zero is also `Rg_*j_!A_U`.
Source: blueprint `lem-trf-devissage-generation`, statement and Step 3
(blueprint: lem-trf-devissage-generation). -/
def trfConstantClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))))

/-- Bounded constructible complexes of finite Tor amplitude are exactly the ambient thick
closure of the lisse flat locally closed extension generators. `T` supplies the coefficient
conventions; X is any separated finite-type scheme over its algebraic closure k.
Source: blueprint `lem-trf-devissage-generation`, statement and Steps 0--2
(blueprint: lem-trf-devissage-generation).

The existing `proEtaleThickGeneration_eq` proves generation with the same closure
family, including its scheme-theoretic closure factorization. To apply it, the coefficient
ring is finite by `Padic.finite_coefficientExtensionRing` and is annihilated by a positive
power of l: the spectral absolute value puts l in the maximal ideal, so l^n belongs to
its nth power, which is the coefficient quotient ideal. Finally a finite subset of the
integers is bounded above and below, and every integer interval is finite. This identifies
the finite support formulation of bounded cohomology with the interval formulation in
`proEtaleThickGeneration_eq`. -/
theorem trf_devissage_generation (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField T.level
      T.level_pos X =
    (@sfProEtaleClosureGenerators X T.coefficientRing inferInstance
      (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
        T.level T.level_pos)).triangEnvelope := by
  let : X.Over (Spec (.of T.datum.k)) := ⟨aX⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of T.datum.k)) := ‹LocallyOfFiniteType aX›
  let : QuasiCompact (X ↘ Spec (.of T.datum.k)) := ‹QuasiCompact aX›
  let : Finite T.coefficientRing :=
    Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
      T.level T.level_pos
  have he := proEtaleThickGeneration_eq T.datum T.coefficients.l
    (Fact.out : T.coefficients.l.Prime) T.coefficients.different T.coefficientRing
    (trf_coefficient_primary T.coefficients.l T.coefficientField T.level T.level_pos) X
  refine Eq.trans ?_ he
  funext K
  apply propext
  change ((Set.Finite _ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
  constructor
  · rintro ⟨⟨hb, hc⟩, ht⟩
    exact ⟨⟨hc, (trf_finite_support_iff _).mp hb⟩, ht⟩
  · rintro ⟨⟨hc, hb⟩, ht⟩
    exact ⟨⟨(trf_finite_support_iff _).mpr hb, hc⟩, ht⟩

private theorem trf_exists_conventions :
    ∃ T : WeilConjectures.TraceFormulaCoefficientConventions.{u},
      CharP T.datum.k 5 ∧ CharP T.coefficientRing 3 ∧ Nontrivial T.coefficientRing := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let D : WeilConjectures.FiniteFieldDatum.{u} := {
    p := 5
    a := 1
    q := 5
    prime := by decide
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one 5).symm
    k₀ := ULift.{u} (ZMod 5)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod 5)) }
  let Q := ULift.{u} (AlgebraicClosure (Padic 3))
  let : IsAlgClosed Q := by
    apply IsAlgClosed.of_exists_root
    intro p _ hp
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero
      (ULift.ringEquiv : Q ≃+* AlgebraicClosure (Padic 3)).toRingHom p
      (ne_of_gt (Polynomial.degree_pos_of_irreducible hp))
    refine ⟨⟨x⟩, ULift.ringEquiv.injective ?_⟩
    change ULift.ringEquiv.toRingHom (p.eval ⟨x⟩) = 0
    rw [← Polynomial.eval₂_at_apply]
    exact hx
  let : Algebra.IsAlgebraic (Padic 3) Q := ULift.algEquiv.symm.isAlgebraic
  let : IsAlgClosure (Padic 3) Q := ⟨inferInstance, inferInstance⟩
  let c : D.CoefficientDatum := {
    l := 3
    different := by decide
    Qbar := Q }
  let T : WeilConjectures.TraceFormulaCoefficientConventions.{u} := {
    datum := D
    coefficients := c
    extension := Padic.finiteCoefficientBase 3 Q
    level := 1
    level_pos := le_refl 1
    X₀ := Over.mk (𝟙 (Spec (.of D.k₀)))
    finite_type := by change LocallyOfFiniteType (𝟙 _); infer_instance
    quasi_compact := by change QuasiCompact (𝟙 _); infer_instance
    separated := by change IsSeparated (𝟙 _); infer_instance }
  have hk : CharP T.datum.k 5 := by
    change CharP (AlgebraicClosure (ULift.{u} (ZMod 5))) 5
    infer_instance
  have h := (Padic.extension_integers_dvr T.coefficients.l T.coefficientField
    (Padic.coefficientExtensionAbsoluteValue T.coefficients.l T.coefficientField)
    (spectralNorm_extends (K := Padic T.coefficients.l)
      (L := T.coefficientField))).choose_spec.choose_spec
  have hgen : Padic.coefficientExtensionIdeal T.coefficients.l T.coefficientField 1 =
      Padic.coefficientExtensionMaximalIdeal T.coefficients.l T.coefficientField := by
    unfold Padic.coefficientExtensionIdeal
    rw [pow_one]
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal
      T.coefficients.l T.coefficientField).IsMaximal := h.2.2.2.2.1
  have hnt : Nontrivial T.coefficientRing := by
    change Nontrivial (Padic.coefficientExtensionIntegers T.coefficients.l
      T.coefficientField ⧸ Padic.coefficientExtensionIdeal
        T.coefficients.l T.coefficientField 1)
    rw [hgen]
    exact Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  have hp : CharP T.coefficientRing 3 := by
    let := hnt
    apply (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 3)).mpr
    -- The proof of primary annihilation uses the given level itself as its exponent.
    have hl : (T.coefficients.l : Padic.coefficientExtensionIntegers
        T.coefficients.l T.coefficientField) ∈
        Padic.coefficientExtensionMaximalIdeal T.coefficients.l T.coefficientField := by
      apply (h.2.1 _).2
      have he := spectralNorm_extends
        (K := Padic T.coefficients.l) (L := T.coefficientField)
        (T.coefficients.l : Padic T.coefficients.l)
      change Padic.coefficientExtensionAbsoluteValue T.coefficients.l T.coefficientField
        (algebraMap (Padic T.coefficients.l) T.coefficientField
          (T.coefficients.l : Padic T.coefficients.l)) = _ at he
      simpa only [map_natCast, Subring.coe_natCast] using he.trans_lt
        (Padic.norm_p_lt_one (p := T.coefficients.l))
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hgen]
    exact hl
  exact ⟨T, hk, hp, hnt⟩

private theorem trf_kummer_finiteType (k : Type u) [Field k] :
    LocallyOfFiniteType (trfKummerStructureMap k) := by
  let j : trfKummerBase k ⟶ Spec (.of (Polynomial k)) :=
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  have : IsOpenImmersion j :=
    IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) Polynomial.X
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C (R := k)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have he : trfKummerStructureMap k =
      j ≫ Spec.map (CommRingCat.ofHom (Polynomial.C (R := k))) := by
    dsimp [j, trfKummerStructureMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro x
    exact (Polynomial.toLaurent_C x).symm
  rw [he]
  infer_instance

set_option maxHeartbeats 800000 in
-- Transport through intrinsic-module and homology equivalences needs extra elaboration steps.
/-- Constant rank-one coefficients do not generate in general: there is a separated
finite-type X with admissible coefficients and a ctf complex outside their thick closure.
Source: blueprint `lem-trf-devissage-generation`, final sentence and Step 3
(blueprint: lem-trf-devissage-generation).

Proof: use the coefficient datum with base field the algebraic closure of F_5,
ell=3, the base coefficient extension, and level one. The coefficient ideal is
maximal, so its quotient is nonzero of characteristic three. The punctured line is
an open subscheme of the affine line and hence has a separated finite-type structure
map. The quadratic cover and its geometric point with a two-cycle give an exact
module fibre functor F, a natural endomorphism t, and a flat lisse generator L.
The endomorphism vanishes on the constant stratum generators but is not nilpotent
on F(L). Nilpotence on each cohomology fibre defines a thick subcategory: powers
intertwine with all maps, and exponents add in extensions. This subcategory contains
the constant generators, so contains their thick envelope. Degree-zero homology of
L recovers L, contradicting nonnilpotence if L belonged to that envelope. The already
proved generation equality puts L in the finite-Tor constructible category. The
separate geometric fibre lemma supplies precisely the local-model and monodromy
calculation; the closure, coefficient, and explicit cover arguments are proved here. -/
theorem exists_trf_constant_coefficients_not_generating :
    ∃ (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
      (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k)),
      LocallyOfFiniteType aX ∧ QuasiCompact aX ∧ IsSeparated aX ∧
      ∃ K : proEtaleDerivedCategory X T.coefficientRing,
        WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField
          T.level T.level_pos X K ∧
        ¬ (@trfConstantClosureGenerators X T.coefficientRing inferInstance
          (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
            T.level T.level_pos)).triangEnvelope K := by
  obtain ⟨T, hk, hA, hnt⟩ := trf_exists_conventions.{u}
  let := hk
  let := hA
  let := hnt
  let : Finite T.coefficientRing :=
    Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
      T.level T.level_pos
  let X := trfKummerBase T.datum.k
  let aX := trfKummerStructureMap T.datum.k
  let : LocallyOfFiniteType aX := trf_kummer_finiteType T.datum.k
  let : IsAffine X := by dsimp [X, trfKummerBase]; infer_instance
  have hqc : QuasiCompact aX := by infer_instance
  have hsep : IsSeparated aX := by dsimp [aX, trfKummerStructureMap]; infer_instance
  let := hqc
  let := hsep
  obtain ⟨F, hF, hFl, hFc, t, L, hmonodromy⟩ :=
    exists_trf_kummer_monodromy T.datum.k T.coefficientRing
  let := hF
  let := hFl
  let := hFc
  let Q := nilpotentFiberHomology F t
  obtain ⟨hQt, hQr⟩ := nilpotentFiberHomology_thick F t
  let := hQt
  let := hQr
  have hiso : (nilpotentFiber F t).IsClosedUnderIsomorphisms := by
    constructor
    intro M N e hM
    obtain ⟨n, hn⟩ := hM
    refine ⟨n, ?_⟩
    have hnatur := t.naturality e.hom
    have hp (n : ℕ) :
        F.map e.hom ≫ ((End.of (t.app N)) ^ n) =
          ((End.of (t.app M)) ^ n) ≫ F.map e.hom := by
      induction n with
      | zero => simp
      | succ n ih =>
        simp only [pow_succ, End.mul_def]
        rw [← Category.assoc, hnatur, Category.assoc, ih, ← Category.assoc]
    apply (cancel_epi (F.map e.hom)).mp
    rw [hp, hn, zero_comp, comp_zero]
  let := hiso
  have hsingle (M : proEtaleRingModules X (proEtaleConstantRing X T.coefficientRing))
      (hM : t.app M = 0) : Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
    intro n
    by_cases hn : n = 0
    · subst n
      apply (nilpotentFiber F t).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm
      exact ⟨1, by change t.app M = 0; exact hM⟩
    · have hz : IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) := by
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.isZero_of_isGE _ 0 n hn
        · exact DerivedCategory.isZero_of_isLE _ 0 n hn
      exact ⟨1, by
        change t.app _ = 0
        exact (F.map_isZero hz).eq_of_src _ _⟩
  have hgen : trfConstantClosureGenerators X T.coefficientRing ≤ Q := by
    rintro K ⟨str, i, j, hj, hw, ⟨e⟩⟩
    let := hj
    exact Q.prop_of_iso e.symm (hsingle _ (hmonodromy.constants str i j hw))
  have hclosed : (trfConstantClosureGenerators X T.coefficientRing).triangEnvelope ≤ Q :=
    (ObjectProperty.triangEnvelope_le_iff
      (P := trfConstantClosureGenerators X T.coefficientRing) (Q := Q)).mpr hgen
  refine ⟨T, X, aX, inferInstance, hqc, hsep,
    (DerivedCategory.singleFunctor _ 0).obj L, ?_, ?_⟩
  · rw [trf_devissage_generation T X aX]
    exact ObjectProperty.le_triangEnvelope _ _ hmonodromy.generator
  · intro h
    have hnil := hclosed _ h 0
    have hzero : IsNilpotent (End.of (t.app L)) :=
      (nilpotentFiber F t).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app L) hnil
    exact hmonodromy.nonnilpotent hzero

end AlgebraicGeometry
