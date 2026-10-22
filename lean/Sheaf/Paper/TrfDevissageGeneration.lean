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
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Triangulated.AmbientThickClosureEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.FieldDiscreteModules
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification

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

/-- Constant rank-one coefficients do not generate in general: there is a separated
finite-type X with admissible coefficients and a ctf complex outside their thick closure.
Source: blueprint `lem-trf-devissage-generation`, final sentence and Step 3
(blueprint: lem-trf-devissage-generation).

Remaining proof plan, node Steps 8--10 (with the comparison of Steps 3--7):
8. Take k = algebraic closure of F_5, X = G_m and A = F_3, realized at l = 3,
E = Q_3, n = 1 in the coefficient conventions. The cover t = u^2 is finite etale of
rank two: its derivative 2u is invertible by
lem-weil-pbc-standard-etale-monic-derivative. thm-galois-fundamental and
cor-galois-lisse-representations construct its rank-one sign local system L, which is
free locally and hence an allowed flat generator.
9. Pull back exactly to Spec k(t) by prop-weil-pbc-inverse-image-modules-exact and
lem-sf-exact-functor-derived-triangulated, retaining the discrete Galois action via
lem-exc-field-discrete-modules. Complexes whose bounded cohomology has a finite
filtration with trivial one-dimensional quotients form a thick subcategory. Intersect
filtrations with submodules, pass to their images for quotients, and concatenate for
extensions. The long exact sequence of lem-sf-derived-homology-long-exact gives triangle
closure; shifts and retracts preserve these conditions.
10. Every constant generator has generic restriction either zero or trivial, by
lemma-weil-pbc-finite-stalk-formula, lem-weil-pbc-closed-immersion-finite,
lem-weil-pbc-extension-by-zero-stalks and lem-fin-closed-immersion. The sign local system
has nontrivial generic action: coprime polynomials cannot satisfy f(t)^2 = t g(t)^2,
so u^2 - t defines a separable quadratic field extension; transitivity follows from
lem-exc-etale-field-galois-classification and agrees with the cover action by
thm-galois-fundamental. Its nontrivial rank-one representation has no filtration by
trivial quotients. Thus L is outside the constant-generated closure. The exact comparison
and generator identifications of Steps 3--7 transport both the constants and this
obstruction to the pro-etale site. -/
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
  sorry

end AlgebraicGeometry
