/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.AdicFiniteRealizationData
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import Sheaf.Paper.AdicFiniteScalarCoherence
import Sheaf.Paper.AdicFiniteConstructibilityComparison
import Sheaf.Paper.AdicClosureScalarCoherence
import Sheaf.Paper.FdIntegralIdentityRationalEquivalence
import Sheaf.Paper.ConstructibleRationalHomComparison
import Sheaf.Paper.RationalContinuousFiltrationModels

/-! # Coherent finite adic realizations

Source: Bhatt--Scholze, Propositions 6.6.11 and 6.8.14(2); HRS Theorem 7.7.
(blueprint: lem-sf-adic-finite-realization-cocone).

The data declarations are reexported from
`AdicFiniteRealizationData`, allowing the proof steps to have independent modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization

private theorem realization_image (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (s : RationalModuleRealization l E T)
    (K : DerivedCategory (pbcModules T (rationalCoefficientSheaf l T E))) :
    finiteFreeTarget T (rationalCoefficientSheaf l T E) K ↔
      ∃ M, Nonempty (s.J.obj M ≅ K) := by
  have hf := ((constructibleRationalHomComparison l E T).2 s).2.1
  have hi := ((constructibleRationalHomComparison l E T).2 s).2.2
  let X : ContinuousRational.Base l :=
    { scheme := T, dimension := Fact.out, prime_unit := Fact.out }
  constructor
  · rintro ⟨⟨a, b, _, ha, hb⟩, hc⟩
    have := ha
    have := hb
    obtain ⟨_, M, _, ⟨e⟩, _⟩ := RationalConeModels.bounded_model l E T s hf hi
      (fun F hF ↦ ContinuousRational.rationalContinuousFiltrationModels l E X s F hF)
      K a b (fun r hr ↦ hr.elim
        (fun h ↦ DerivedCategory.isZero_of_isGE K a r h)
        (fun h ↦ DerivedCategory.isZero_of_isLE K b r h)) hc
    exact ⟨(pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M, ⟨e⟩⟩
  · rintro ⟨⟨M⟩, ⟨e⟩⟩
    obtain ⟨⟨a, b, ha, hb⟩, hc⟩ := s.constructible M
    let q : (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).obj M.obj ≅ K :=
      (eqToIso (s.objects M)).symm ≪≫ e
    have := ha
    have := hb
    have hge := DerivedCategory.TStructure.t.isGE_of_iso q a
    have hle := DerivedCategory.TStructure.t.isLE_of_iso q b
    refine ⟨⟨min a b, b, min_le_right _ _, ?_, hle⟩, fun r ↦ ?_⟩
    · exact DerivedCategory.TStructure.t.isGE_of_ge K (min a b) a (min_le_left _ _)
    · obtain ⟨t, ht⟩ := hc r
      refine ⟨t, fun j ↦ ?_⟩
      have := ht j
      exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1}
        ((proEtaleModuleInverseImage (t.immersion j)
          (rationalCoefficientSheaf l T E)).mapIso
            ((DerivedCategory.homologyFunctor _ r).mapIso q))

private theorem core_exists (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))] : Nonempty (Core l T) := by
  classical
  let stage (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    (fdIntegralIdentityRationalEquivalence D l hl (PadicAlgCl l) T E).choose
  obtain ⟨raw⟩ := fdCompletionInverseScalarCoherence D l hl (PadicAlgCl l) T stage
  let realization (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    Classical.choice (rationalModuleRealizationFunctor l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T)
  refine ⟨⟨stage, raw, realization, ?_, ?_⟩⟩
  · intro E K L
    have hf := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.1
    have hi := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.2
    exact (Functor.FullyFaithful.ofFullyFaithful (realization E).J).map_bijective K L
  · intro E K
    exact realization_image l (pbcFiniteField.{u} l (PadicAlgCl l) E) T (realization E) K

/-- Coherent continuous realization of every raw finite coefficient stage, with the
specified quotient-completion scalar comparisons, including identity and towers.
Source: BS Proposition 6.6.11, Definition 6.8.8 and Proposition 6.8.14(2);
HRS Theorem 7.7 and Lemma 7.9
(blueprint: lem-sf-adic-finite-realization-cocone).

Proof:
1. Finite type over the field gives local Noetherianity, compactness, finite
Krull dimension and quasi-separatedness. The finite base field has characteristic p;
its algebraic closure has the same characteristic. Since l is prime and differs
from p, it is a unit in k, hence in every stalk of T.
2. For every finite E use fdIntegralIdentityRationalEquivalence for the raw stage
comparison and fdCompletionInverseScalarCoherence for its normalized inverse scalar
family. Use rationalModuleRealizationFunctor for the continuous realization.
3. constructibleRationalHomComparison gives fullness and faithfulness. To prove the
image criterion, use rationalContinuousFiltrationModels for each cohomology sheaf
and RationalConeModels.bounded_model to lift the finite truncation tower. Conversely
the realization's constructible field gives the strata, and its objects equation
transports cohomology and degree bounds along the proposed isomorphism. Replace a
lower bound by its minimum with the upper bound to order the interval.
4. adic_finite_scalar_coherence supplies the coefficient and theta comparisons
with their integral commuting diagram, actual raw associator, and multiplication unit.
5. adic_finite_constructibility_comparison supplies the normalized ring cocone
and the internal and ordinary section-module constructibility criteria.
6. adic_closure_scalar_coherence transports the finite coherence equations to the
native closure ring. Insert these witnesses into the unchanged Data fields. -/
theorem adic_finite_realization_cocone (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (T : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    ∃ (_hN : IsNoetherian T.left)
      (_hD : Fact (∃ n : ℕ, topologicalKrullDim T.left ≤ n))
      (_hI : Fact (∀ x : T.left, IsUnit (l : T.left.presheaf.stalk x))),
      QuasiSeparatedSpace T.left ∧ Nonempty (Data l T.left) := by
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have hN : IsNoetherian T.left := ⟨⟩
  have hD : Fact (∃ n : ℕ, topologicalKrullDim T.left ≤ n) :=
    ⟨exists_topologicalKrullDim_le T.hom⟩
  have hI : Fact (∀ x : T.left, IsUnit (l : T.left.presheaf.stalk x)) := by
    let : Fintype D.k₀ := Fintype.ofFinite _
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    have hu : IsUnit (l : D.k) := isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) _hl.symm)
    let f := (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ T.hom.appTop
    refine ⟨fun x ↦ ?_⟩
    simpa only [map_natCast] using (hu.map f.hom).map
      (T.left.presheaf.germ ⊤ x (by trivial)).hom
  have hQ : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
  obtain ⟨C⟩ := core_exists D l _hl T.left
  obtain ⟨B, ⟨H⟩⟩ := adic_finite_scalar_coherence l T.left C
  obtain ⟨R, hF, hR, hFS, hRS⟩ := adic_finite_constructibility_comparison l T.left C B
  obtain ⟨ht, hi⟩ := adic_closure_scalar_coherence l T.left C B H R
  exact ⟨hN, hD, hI, hQ, ⟨{
    toCore := C
    scalar := B
    coherence := H
    closure := R
    finite_constructibility := hF
    closure_constructibility := hR
    finite_sections := hFS
    closure_sections := hRS
    closure_tower := ht
    closure_identity := hi }⟩⟩

end WeilConjectures.AdicFiniteRealization

