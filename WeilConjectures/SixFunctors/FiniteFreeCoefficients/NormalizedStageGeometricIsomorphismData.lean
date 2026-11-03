/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateInvertible
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteBridgeFoundations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageClosedIsomorphismData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomIsomorphismData
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! Geometric stage maps are invertible on ctf objects after normalized scalar change.

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

private theorem stageMateChangeAdjunction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G H : D ⥤ C} {F' : C' ⥤ D'} {G' H' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F ⊣ H) (b : F' ⊣ G') (b' : F' ⊣ H')
    (Q : C ⥤ C') (T : D ⥤ D') (d : F ⋙ T ≅ Q ⋙ F') (M : D)
    (x : Etale.CoefficientCounitMateData a' b' Q T d M)
    (y : Etale.CoefficientCounitMateData a b Q T d M)
    (hi : IsIso x.hom) : IsIso y.hom := by
  let e := a.rightAdjointUniq a'
  let e' := b.rightAdjointUniq b'
  have he : F.map (e.hom.app M) ≫ a'.counit.app M = a.counit.app M :=
    a.rightAdjointUniq_hom_app_counit a' M
  have he' : F'.map (e'.hom.app (T.obj M)) ≫ b'.counit.app (T.obj M) =
      b.counit.app (T.obj M) := b.rightAdjointUniq_hom_app_counit b' _
  have h : y.hom ≫ e'.hom.app (T.obj M) = Q.map (e.hom.app M) ≫ x.hom := by
    apply (b'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [he', y.counit, x.counit]
    have hn := d.inv.naturality (e.hom.app M)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← T.map_comp, he]
  have : IsIso x.hom := hi
  have : IsIso (Q.map (e.hom.app M) ≫ x.hom) := inferInstance
  have : IsIso (y.hom ≫ e'.hom.app (T.obj M)) := h.symm ▸ this
  exact (isIso_comp_right_iff _ _).1 this

/-- Geometric stage maps are invertible on ctf objects after normalized scalar change.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-geometric-isomorphism-data).

Proof: Apply the closed and internal-Hom component theorems to the given inputs and normalized
tensorators. The dualizing fields are proved directly. Stage ramification supplies an annihilating
power of l, which is invertible over D.k. The regular unit is ctf, so exceptional finite-Tor
stability gives ctf membership of the ordinary dualizing object. The invertible omegaBridge and
preservation of ctf under nu give the pro-etale assertion. For invertibility, use the finite-stage
mate theorem at the regular unit for the chosen compactification. A proved abstract calculation
with rightAdjointUniq identifies its counit mate with the canonical exceptional counit mate up to
isomorphisms. Compose with the upper image of the scalar-unit isomorphism; this is omegaMap by its
definition. The four factors defining proOmegaMap are then all isomorphisms. Collect the four
fields without changing any of their maps or domains. -/
theorem normalized_stage_geometric_isomorphism_data
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (μ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.TensorComparison pro a.ringMap X)
    (hμ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.NormalizedTensor pro a.ringMap X (μ pro a)) :
    ∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro) := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI := finiteTypeNoetherian D.k X
  letI := c.hasCompactification
  have ho (s : Stage l E) : Ctf s.ring X (omega s.ring c) := by
    letI : HasInvertibleExponent s.ring (Spec (.of D.k)) :=
      stageInvertibleExponent D.k D.p l hl s (Spec (.of D.k))
    apply (ctf_iff_source s.ring X _).2
    exact Etale.constructibleFiniteTor_dualizingComplex s.ring (𝟙 (Spec (.of D.k)))
      (X ↘ Spec (.of D.k)) (Etale.constructibleFiniteTor_unit s.ring)
  have hctf (pro : Bool) (s : Stage l E) :
      Sites.Ctf pro s.ring X (Sites.omega pro s.ring c) := by
    cases pro
    · exact ho s
    · letI := (finite_ring_site_bridge_foundations s.ring i c).2
      exact (ProEtale.DerivedCategory.constructibleFiniteTor _ X).prop_of_iso
        (asIso (Sites.omegaBridge s.ring c))
        (ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory s.ring
          ((ctf_iff_source s.ring X _).1 (ho s)))
  have hω {s t : Stage l E} (a : Arrow s t) : IsIso (omegaMap a.ringMap c) := by
    have hm : IsIso (Etale.ExceptionalCoefficients.mateMap a.ringMap
        (X ↘ Spec (.of D.k)) (𝟙_ _)) := by
      letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
      letI : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) :=
        ⟨by change (X ↘ Spec (.of D.k)) ≫ 𝟙 _ = _; exact Category.comp_id _⟩
      let d := HasCompactification.compactification (X ↘ Spec (.of D.k))
      let Q := Etale.scalarExtension a.ringMap X
      let T := Etale.scalarExtension a.ringMap (Spec (.of D.k))
      let δ := Etale.ExceptionalCoefficients.compactSupportIso a.ringMap d
      let aS := Etale.rightDerivedUpperShriekAdjunction s.ring (X ↘ Spec (.of D.k))
      let aT := Etale.rightDerivedUpperShriekAdjunction t.ring (X ↘ Spec (.of D.k))
      let bS := etaleAdjunction s.ring d
      let bT := etaleAdjunction t.ring d
      have hs := etale_finite_stage_mate_invertible D.k D.p l
        (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) D.prime.pos hl E
        (X ↘ Spec (.of D.k)) a d (𝟙_ _) (Etale.constructibleFiniteTor_unit s.ring)
      have hs' : IsIso (Etale.coefficientCounitMateData bS bT Q T δ (𝟙_ _)).hom := by
        unfold Etale.coefficientCounitMateData counitTranspose
        change IsIso (bT.homEquiv _ _ (δ.inv.app _ ≫ T.map (bS.counit.app _)))
        rw [← Etale.ExceptionalCoefficients.comparisonInverse_eq]
        exact hs
      have ht := stageMateChangeAdjunction aS bS aT bT Q T δ (𝟙_ _)
        (Etale.coefficientCounitMateData bS bT Q T δ (𝟙_ _))
        (Etale.coefficientCounitMateData aS aT Q T δ (𝟙_ _)) hs'
      unfold Etale.coefficientCounitMateData counitTranspose at ht
      change IsIso (aT.homEquiv _ _ (δ.inv.app _ ≫ T.map (aS.counit.app _))) at ht
      rw [← Etale.ExceptionalCoefficients.comparisonInverse_eq] at ht
      exact ht
    dsimp only [omegaMap]
    infer_instance
  intro pro
  refine ⟨?_, ?_, ?_, hctf pro⟩
  · exact normalized_stage_closed_isomorphism_data D l hl E X Z i pro
  · intro s t a
    cases pro
    · exact hω a
    · letI := hω a
      letI := (finite_ring_site_bridge_foundations s.ring i c).2
      letI := (finite_ring_site_bridge_foundations t.ring i c).2
      dsimp only [Sites.stageOmegaMap, Sites.proOmegaMap]
      have hi : IsIso (Sites.inverseOnDomain (Sites.omegaBridge s.ring c)) := by
        rw [Sites.inverseOnDomain, dif_pos (by infer_instance)]
        infer_instance
      infer_instance
  · intro s t a K M hK hM
    exact normalized_stage_hom_isomorphism_data D l hl E X pro a (μ pro a)
      (hμ pro a) K M hK hM

attribute [-instance] CategoryTheory.catToReflQuiver in
end WeilConjectures.FiniteFreeCoefficients
