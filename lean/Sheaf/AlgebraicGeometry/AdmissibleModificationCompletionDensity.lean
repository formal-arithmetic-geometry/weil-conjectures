/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleCompletionPointSystem
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AdmissibleCompletionFiberIso
import Sheaf.AlgebraicGeometry.AdmissibleCompletionStrictLocalCongruence
import Sheaf.AlgebraicGeometry.AdmissibleModificationSystem
import Sheaf.RingTheory.ColimitQuotientComparison

/-! # Congruences on corresponding admissible blowups

Source: ILO, Travaux de Gabber, XX 4.4, p.374, final Note; XX 2.4.3--2.4.4,
pp.364--365 (blueprint: lem-per-admissible-modification-completion-density).

The scheme comparison is the reduction of the canonical Rees blowup morphism.
The ring comparison is induced on colimits by its canonical pointed strict-local maps.
No flatness, Noetherian, excellence, separatedness of the completion map, or regularity
of the generator in the principal-ideal clause is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The quotient map induced by A → its I-adic completion, with target ideal I^n A'.
Source: ILO XX 2.4.3, p.364; XX 4.4, p.374
(blueprint: lem-per-admissible-modification-completion-density). -/
noncomputable def completionPowerQuotientMap {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ n →+* AdicCompletion I A ⧸ (I ^ n).map (algebraMap A (AdicCompletion I A)) :=
  Ideal.quotientMap ((I ^ n).map (algebraMap A (AdicCompletion I A)))
    (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map

/-- The square needed to restrict the completion comparison to a closed fibre commutes.
Source: ILO XX 2.4.3, p.364; XX 4.4 final Note, p.374
(blueprint: lem-per-admissible-modification-completion-density).

Proof: both composites are spectra of the ring map a ↦ the class of a in A'/I^n A'.
The equality on quotient representatives is Ideal.quotientMap_comp_mk; apply the
contravariant functoriality of Spec. This is the well-definedness part of the canonical
closed-fibre map, not an assumption on that map. -/
theorem completionPowerQuotientMap_square {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((I ^ n).map (algebraMap A (AdicCompletion I A))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) =
    Spec.map (CommRingCat.ofHom (completionPowerQuotientMap I n)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Reduction of the actual blowup comparison to the nth infinitesimal closed fibres.
Its components are the canonical Rees blowup morphism and Spec of the quotient map.
Source: ILO XX 4.4 final Note, p.374; XX 2.4.3, p.364
(blueprint: lem-per-admissible-modification-completion-density). -/
noncomputable def admissibleCompletionFiberMap {A : Type u} [CommRing A]
    (I J : Ideal A) (n : ℕ) :
    pullback (AffineBlowup.toSpec (J.map (algebraMap A (AdicCompletion I A))))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((I ^ n).map (algebraMap A (AdicCompletion I A)))))) ⟶
      pullback (AffineBlowup.toSpec J)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :=
  pullback.map _ _ _ _ (AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl)
    (Spec.map (CommRingCat.ofHom (completionPowerQuotientMap I n)))
    (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))))
    (AffineBlowup.hom_toSpec (algebraMap A (AdicCompletion I A)) rfl).symm
    (completionPowerQuotientMap_square I n)

/-- The stage structural maps induce the same A-map to the colimit. -/
private theorem admissibleCompletion_base_colimit
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (S : AdmissibleCompletionPointSystem I Ω) (J : AdmissibleBlowupIndex I) :
    S.base.app J ≫ colimit.ι S.rings J = S.sourceBaseMap hI := by
  classical
  let J₀ : AdmissibleModificationSystem.Index I := ⟨I, hI, rfl⟩
  let J₁ : AdmissibleModificationSystem.Index I :=
    ⟨J.ideal, J.unop.2.1, PrimeSpectrum.zeroLocus_eq_iff.mpr J.unop.2.2⟩
  obtain ⟨K, ⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    (AdmissibleModificationSystem.admissibleModificationSystem I hI).1.2.2 J₁ J₀
  let K' : AdmissibleBlowupIndex I := Opposite.op
    ⟨K.val, K.property.1, PrimeSpectrum.zeroLocus_eq_iff.mp K.property.2⟩
  let a : J ⟶ K' := (InducedCategory.homMk (Over.homMk f hf)).op
  let b : Opposite.op ⟨I, hI, rfl⟩ ⟶ K' :=
    (InducedCategory.homMk (Over.homMk g hg)).op
  have hbase {j k : AdmissibleBlowupIndex I} (e : j ⟶ k) :
      S.base.app j ≫ colimit.ι S.rings j = S.base.app k ≫ colimit.ι S.rings k := by
    have he : S.base.app j ≫ S.rings.map e = S.base.app k := by
      have he := S.base.naturality e
      change 𝟙 (CommRingCat.of A) ≫ S.base.app k = S.base.app j ≫ S.rings.map e at he
      simpa only [Category.id_comp] using he.symm
    rw [← colimit.w S.rings e, ← Category.assoc, he]
  exact (hbase a).trans (hbase b).symm

/-- The infinitesimal-fibre isomorphisms and the induced congruences on strict-local
colimits, including the principal exceptional-ideal case.
The target ideals in the quotient maps are written as extensions along the actual map
u. Ideal.map_map identifies them with I^n C, and Ideal.map_span and map_pow identify the
last target with the ideal generated by (u φ)^n. Thus these are exactly the specified
quotient maps, with no independently chosen isomorphisms.
Source: ILO XX 4.4 final Note, p.374; XX 2.4.3--2.4.4, pp.364--365
(blueprint: lem-per-admissible-modification-completion-density).

Proof: the fibre comparison follows from admissibleCompletion_fiber_iso by
pullback extensionality, using the two specified projection identities. For the ring
comparison use admissibleCompletion_strictLocal_congruence at every index. A common
dominating blowup identifies each structural A-map with sourceBaseMap. The universal
property of the ring colimits then transports the stage quotient inverses to an
inverse of the colimit quotient map, by colimit_quotientMap_bijective. This avoids
choosing finite representatives in a filtered colimit. Finally Ideal.map_pow and
Ideal.span_singleton_pow turn I^n B into the ideal generated by φ^n whenever IB = (φ). -/
theorem admissibleModification_completion_density {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] (hI : I.FG) :
    (∀ (J : Ideal A), J.FG → J.radical = I.radical →
      ∀ (n : ℕ), 1 ≤ n → IsIso (admissibleCompletionFiberMap I J n)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (S : AdmissibleCompletionPointSystem I Ω) (n : ℕ), 1 ≤ n →
      Function.Bijective
        (Ideal.quotientMap
          (((I ^ n).map (S.sourceBaseMap hI).hom).map S.colimitMap.hom)
          S.colimitMap.hom Ideal.le_comap_map)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (S : AdmissibleCompletionPointSystem I Ω) (φ : S.sourceRing),
      I.map (S.sourceBaseMap hI).hom = Ideal.span {φ} →
      ∀ (n : ℕ), 1 ≤ n →
      Function.Bijective
        (Ideal.quotientMap ((Ideal.span {φ ^ n}).map S.colimitMap.hom)
          S.colimitMap.hom Ideal.le_comap_map)) := by
  have hfiber : ∀ (J : Ideal A), J.FG → J.radical = I.radical →
      ∀ (n : ℕ), 1 ≤ n → IsIso (admissibleCompletionFiberMap I J n) := by
    intro J hJ hJI n hn
    obtain ⟨e, he₁, he₂⟩ := admissibleCompletion_fiber_iso I hI J hJ hJI n hn
    have he : e.hom = admissibleCompletionFiberMap I J n := by
      apply pullback.hom_ext
      · simpa only [admissibleCompletionFiberMap, pullback.map, pullback.lift_fst] using he₁
      · simpa only [admissibleCompletionFiberMap, pullback.map, pullback.lift_snd,
          completionPowerQuotientMap] using he₂
    rw [← he]
    infer_instance
  have hcolimit : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (S : AdmissibleCompletionPointSystem I Ω) (n : ℕ), 1 ≤ n →
      Function.Bijective
        (Ideal.quotientMap
          (((I ^ n).map (S.sourceBaseMap hI).hom).map S.colimitMap.hom)
          S.colimitMap.hom Ideal.le_comap_map) := by
    intro Ω _ _ S n hn
    apply CommRingCat.colimit_quotientMap_bijective (.of A) (I ^ n) S.rings S.completedRings
      S.base (S.sourceBaseMap hI)
    · intro J
      exact admissibleCompletion_base_colimit I hI S J
    · intro J
      exact admissibleCompletion_strictLocal_congruence I hI S J n hn
  refine ⟨hfiber, hcolimit, ?_⟩
  intro Ω _ _ S φ hφ n hn
  have hh := hcolimit Ω S n hn
  rw [Ideal.map_pow, hφ, Ideal.span_singleton_pow] at hh
  exact hh

end AlgebraicGeometry
