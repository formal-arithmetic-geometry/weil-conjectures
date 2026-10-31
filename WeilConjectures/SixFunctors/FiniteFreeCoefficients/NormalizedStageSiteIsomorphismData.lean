/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations

/-! The internal-Hom site map is invertible at the actual finite coefficient stages.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem stageAnnihilator
    {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (s : Stage l E) :
    ∃ n : ℕ, (l : s.ring) ^ n = 0 := by
  obtain ⟨e, z, hz, hideal, _⟩ := stage_ramification s
  let n : ℕ := (e : ℕ) * (s.exponent : ℕ)
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have hlmem : (l : s.integers) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) := by
    have hgen : Ideal.span
        ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) =
        Padic.coefficientExtensionMaximalIdeal l s.field :=
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    rw [hgen]
    apply (hF.2.1 _).mpr
    change spectralNorm (Padic l) s.field (l : s.field) < 1
    rw [← map_natCast (algebraMap (Padic l) s.field) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  refine ⟨n, ?_⟩
  have hm : (l : s.integers) ^ n ∈ s.ideal := by
    change _ ∈ Ideal.span ({s.parameter} : Set s.integers) ^ (s.exponent : ℕ)
    rw [hideal]
    exact Ideal.pow_mem_pow hlmem n
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

private theorem coefficientExponentUnit
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] (n : ℕ) :
    IsUnit ((l ^ n : ℕ) : Γ(T, ⊤)) := by
  have hnonzero : (l : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) hlp.symm
  have hu : IsUnit ((l ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hnonzero)
  let r : k →+* Γ(T, ⊤) :=
    (T ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using hu.map r

private theorem stageInvertibleExponent
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s : Stage l E)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] : HasInvertibleExponent s.ring T := by
  obtain ⟨n, hn⟩ := stageAnnihilator s
  exact ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, by simpa using hn,
    coefficientExponentUnit k p l hlp T n⟩

/-- The prescribed internal-Hom site map is invertible at each finite coefficient stage.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-site-isomorphism-data).

Proof: Stage ramification puts a power of l in the defining ideal of each stage ring.
Since l differs from the residue characteristic, that exponent is invertible on X. Equip D.k
with its algebraic-closure structure over ZMod D.p through D.k₀. Convert the recorded finite-Tor
constructibility of K and bounded constructibility of M to the source predicates. The generic
finite-ring derived site Hom theorem then proves invertibility of the prescribed evaluation map
directly for the actual stage ring. No change of coefficient field or ring is involved. -/
theorem normalized_stage_site_isomorphism_data
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ (s : Stage l E) (K M : Cat s.ring X),
      Ctf s.ring X K → Ctf s.ring X M → IsIso (Sites.siteHom s.ring X K M) := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Algebra (ZMod D.p) D.k₀ := ZMod.algebra D.k₀ D.p
  letI : Algebra (ZMod D.p) D.k :=
    ((algebraMap D.k₀ D.k).comp (algebraMap (ZMod D.p) D.k₀)).toAlgebra
  letI : IsScalarTower (ZMod D.p) D.k₀ D.k := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsAlgClosure (ZMod D.p) D.k := IsAlgClosure.ofAlgebraic (ZMod D.p) D.k₀ D.k
  intro s K M hK hM
  letI : HasInvertibleExponent s.ring X :=
    stageInvertibleExponent D.k D.p l hl s X
  exact ProEtale.isIso_siteHom s.ring (p := D.p) (X ↘ Spec (.of D.k)) K M
    ((ctf_iff_source s.ring X K).mp hK)
    ((boundedConstructible_iff_source s.ring X M).mp hM.1)

end WeilConjectures.FiniteFreeCoefficients
