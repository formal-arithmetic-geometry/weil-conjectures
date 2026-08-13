/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Compactification.SchemeTheoreticImage

/-!

# The dense-source valuative criterion

This file provides the valuation-theoretic inputs of the two-open compactification
theorem, following the blueprint chapter "Nagata compactification", section
"The dense-source valuative criterion" (proof order items 38–42):

- `ValuationSubring.comapResidue`: the **composite of two valuation rings** (blueprint:
  `lemma:nagata-composite-valuation-ring`; proof order item 39): the preimage in a
  valuation subring `A ⊆ K` of a valuation subring `A''` of its residue field is again
  a valuation subring of `K`; it contains the maximal ideal of `A`
  (`mem_comapResidue_of_not_isUnit`) and its residue map onto `A''` is surjective with
  kernel the trace of the maximal ideal of `A`
  (`comapResidueRes_surjective`, `ker_comapResidueRes`), which is the statement
  `C/𝔪' ≅ A''` of the blueprint. Its fraction field is `K`, as for every valuation
  subring of `K`;
- `ValuationSubring.comap_eq_of_le_comap`: the **intersection with a dominating
  valuation ring** (blueprint: `lemma:nagata-valuation-intersection`; proof order
  item 40): if a valuation subring `B ⊆ L` dominates the image of a valuation subring
  `A ⊆ K` along `K ⟶ L`, then `K ∩ B = A`, i.e. `B.comap f = A`. This is the
  maximality of valuation subrings in the domination order (Stacks Tag 052K);
- `ValuationSubring.exists_dominating_extension`: **extension of a valuation ring to a
  field extension** (Stacks Project Tag 00IA; blueprint:
  `lemma:nagata-valuation-ring-extension`; proof order item 41), derived from
  Mathlib's Chevalley extension theorem `LocalSubring.exists_le_valuationSubring`;
- `AlgebraicGeometry.ValuationProbe` and
  `AlgebraicGeometry.exists_valuationRing_through_schemeDense_raw`: the **valuation
  probe through a schematically dense source** (Stacks Project Tag 02JQ; blueprint:
  `lemma:nagata-dense-valuation-probe-exists`; proof order item 38);
- `AlgebraicGeometry.ValuativeCriterion.universallyClosed_of_dense` and
  `AlgebraicGeometry.ValuativeCriterion.isSeparated_of_dense`: the **dense-source
  valuative criterion** (Stacks Project Tag 0894; blueprint:
  `lemma:nagata-dense-source-valuative`; proof order item 42): unique valuation
  lifting against squares whose generic point passes through a dense source implies
  universal closedness, and separatedness when the morphism is quasi-separated.

Items 38–41 are fully proved. The dense-source valuative criterion itself (item 42,
Stacks Tag 0894) is recorded with `sorry`: its proof is the reduction of an arbitrary
valuative square to one through the dense source, whose ingredients — the valuation
probe (item 38), the composite valuation ring (item 39), the dominating extension
(item 41) and the intersection lemma (item 40) — are all available in this file.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

open IsLocalRing

/-- The inverse of an element of a valuation subring which is a unit of the subring
belongs to the subring. -/
theorem inv_mem_of_isUnit {x : K} (hx : x ∈ A) (hu : IsUnit (⟨x, hx⟩ : A)) :
    x⁻¹ ∈ A := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Aˣ) : A) * ⟨x, hx⟩ = 1 := by
    rw [← hu]
    exact u.inv_mul
  have h2 : (((u⁻¹ : Aˣ) : A) : K) * x = 1 := by
    have := congrArg (Subtype.val : A → K) h1
    simpa using this
  rw [inv_eq_of_mul_eq_one_left h2]
  exact SetLike.coe_mem (((u⁻¹ : Aˣ) : A))

/-- The residue of a non-unit of a valuation subring vanishes. -/
theorem residue_eq_zero_of_not_isUnit {x : A} (h : ¬IsUnit x) :
    IsLocalRing.residue A x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr ((IsLocalRing.mem_maximalIdeal _).mpr
    (_root_.mem_nonunits_iff.mpr h))

/-- **The composite of two valuation rings** (blueprint:
`lemma:nagata-composite-valuation-ring`; proof order item 39): the preimage in a
valuation subring `A ⊆ K` of a valuation subring `A''` of the residue field of `A` is
a valuation subring of `K`. Its fraction field is `K` (as for every valuation subring
of `K`), it contains the maximal ideal of `A`
(`ValuationSubring.mem_comapResidue_of_not_isUnit`), and its quotient by that ideal is
`A''` (`ValuationSubring.comapResidueRes_surjective`,
`ValuationSubring.ker_comapResidueRes`). -/
def comapResidue (A'' : ValuationSubring (ResidueField A)) : ValuationSubring K where
  __ := (A''.toSubring.comap (residue A)).map A.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hres : residue A ⟨x, hxA⟩ ∈ A''
      · exact Or.inl (Subring.mem_map.mpr ⟨⟨x, hxA⟩, Subring.mem_comap.mpr hres, rfl⟩)
      · -- `x` is a unit of `A`, else its residue would be `0 ∈ A''`
        have hunit : IsUnit (⟨x, hxA⟩ : A) := by
          by_contra hnu
          exact hres (by
            rw [residue_eq_zero_of_not_isUnit A hnu]
            exact zero_mem _)
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hunit.ne_zero (by rfl)
        have hxinvA : x⁻¹ ∈ A := A.inv_mem_of_isUnit hxA hunit
        refine Or.inr (Subring.mem_map.mpr
          ⟨⟨x⁻¹, hxinvA⟩, Subring.mem_comap.mpr ?_, rfl⟩)
        have hmul : residue A ⟨x, hxA⟩ * residue A ⟨x⁻¹, hxinvA⟩ = 1 := by
          rw [← map_mul, show (⟨x, hxA⟩ : A) * ⟨x⁻¹, hxinvA⟩ = 1 from
            Subtype.ext (mul_inv_cancel₀ hx0), map_one]
        rcases A''.mem_or_inv_mem (residue A ⟨x, hxA⟩) with h | h
        · exact absurd h hres
        · change residue A ⟨x⁻¹, hxinvA⟩ ∈ A''
          rwa [show residue A ⟨x⁻¹, hxinvA⟩ = (residue A ⟨x, hxA⟩)⁻¹ from
            eq_inv_of_mul_eq_one_left (mul_comm (residue A ⟨x, hxA⟩) _ ▸ hmul)]
    · -- `x⁻¹` lies in the maximal ideal of `A`, so its residue is `0 ∈ A''`
      have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
      have hnu : ¬IsUnit (⟨x⁻¹, hxinv⟩ : A) := by
        intro hu
        have := A.inv_mem_of_isUnit hxinv hu
        rw [inv_inv] at this
        exact hxA this
      refine Or.inr (Subring.mem_map.mpr
        ⟨⟨x⁻¹, hxinv⟩, Subring.mem_comap.mpr ?_, rfl⟩)
      change residue A ⟨x⁻¹, hxinv⟩ ∈ A''
      rw [residue_eq_zero_of_not_isUnit A hnu]
      exact zero_mem _

variable (A'' : ValuationSubring (ResidueField A))

theorem mem_comapResidue {x : K} :
    x ∈ A.comapResidue A'' ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ A'' := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp h
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, hres⟩
    exact Subring.mem_map.mpr ⟨⟨x, hx⟩, hres, rfl⟩

/-- The composite valuation ring is contained in `A`. -/
theorem comapResidue_le : (A.comapResidue A'').toSubring ≤ A.toSubring := by
  intro x hx
  exact (mem_comapResidue A A''|>.mp hx).1

/-- The composite valuation ring contains the maximal ideal of `A` (blueprint:
`𝔪' ⊆ C`). -/
theorem mem_comapResidue_of_not_isUnit {x : K} (hx : x ∈ A)
    (h : ¬IsUnit (⟨x, hx⟩ : A)) : x ∈ A.comapResidue A'' :=
  (mem_comapResidue A A'').mpr ⟨hx, by
    rw [residue_eq_zero_of_not_isUnit A h]
    exact zero_mem _⟩

theorem residue_inclusion_mem (c : A.comapResidue A'') :
    residue A (Subring.inclusion (A.comapResidue_le A'') c) ∈ A'' := by
  obtain ⟨hx, hres⟩ := (mem_comapResidue A A'').mp c.2
  rwa [show Subring.inclusion (A.comapResidue_le A'') c = ⟨(c : K), hx⟩ from
    Subtype.ext rfl]

/-- The residue map of the composite valuation ring onto the second factor: the
restriction of the residue map of `A` along the inclusion `C ⊆ A`, corestricted
to `A''`. -/
def comapResidueRes : A.comapResidue A'' →+* A''.toSubring :=
  ((residue A).comp (Subring.inclusion (A.comapResidue_le A''))).codRestrict
    A''.toSubring (A.residue_inclusion_mem A'')

/-- The residue map of the composite valuation ring onto `A''` is surjective. This is
the surjectivity half of the identification `C/𝔪' ≅ A''` of the blueprint. -/
theorem comapResidueRes_surjective :
    Function.Surjective (A.comapResidueRes A'') := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) b
  have hmem : (a : K) ∈ A.comapResidue A'' :=
    (mem_comapResidue A A'').mpr ⟨a.2, by rwa [ha]⟩
  refine ⟨⟨(a : K), hmem⟩, ?_⟩
  apply Subtype.ext
  change residue A (Subring.inclusion (A.comapResidue_le A'') ⟨(a : K), hmem⟩) = b
  rw [show Subring.inclusion (A.comapResidue_le A'') ⟨(a : K), hmem⟩ = a from
    Subtype.ext rfl, ha]

/-- The kernel of the residue map of the composite valuation ring is the trace of the
maximal ideal of `A`. Together with `comapResidueRes_surjective` this is the
identification `C/𝔪' ≅ A''` of the blueprint. -/
theorem ker_comapResidueRes :
    RingHom.ker (A.comapResidueRes A'') =
      (IsLocalRing.maximalIdeal A).comap (Subring.inclusion (A.comapResidue_le A'')) := by
  ext c
  rw [RingHom.mem_ker, Ideal.mem_comap]
  constructor
  · intro h
    have h0 : residue A (Subring.inclusion (A.comapResidue_le A'') c) = 0 :=
      congrArg Subtype.val h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · intro h
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

section Domination

variable {L : Type*} [Field L]

/-- **Intersection with a dominating valuation ring** (blueprint:
`lemma:nagata-valuation-intersection`; proof order item 40): if a valuation subring
`B` of a field extension `L` of `K` dominates a valuation subring `A ⊆ K` — that is,
`A ≤ B.comap f` in the domination order of local subrings of `K` — then
`K ∩ B = A`, i.e. `B.comap f = A`. This is the maximality of valuation subrings in
the domination order (Stacks Project Tag 052K). -/
theorem comap_eq_of_le_comap (f : K →+* L) (A : ValuationSubring K)
    (B : ValuationSubring L) (h : A.toLocalSubring ≤ (B.comap f).toLocalSubring) :
    B.comap f = A :=
  ValuationSubring.toLocalSubring_injective
    (le_antisymm (A.isMax_toLocalSubring h) h)

/-- **Extension of a valuation ring to a field extension** (Stacks Project Tag 00IA;
blueprint: `lemma:nagata-valuation-ring-extension`; proof order item 41): for every
field extension `f : K ⟶ L` and every valuation subring `A ⊆ K` there is a valuation
subring `B ⊆ L` dominating the image of `A`; its fraction field is `L` since it is a
valuation subring of `L`. Combined with `comap_eq_of_le_comap` this gives
`K ∩ B = A`. -/
theorem exists_dominating_extension (f : K →+* L) (A : ValuationSubring K) :
    ∃ B : ValuationSubring L, A.toLocalSubring ≤ (B.comap f).toLocalSubring := by
  obtain ⟨B, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp A.subtype)
  have hsub : A.toLocalSubring.toSubring ≤ (B.comap f).toLocalSubring.toSubring :=
    fun x hx ↦ hmem ⟨x, hx⟩
  refine ⟨B, hsub, ⟨fun a ha ↦ ?_⟩⟩
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  -- the image of `a` in `B` is a unit with inverse the image of `v`
  have hval : (a : K) * (v : K) = 1 := by
    have := congrArg (Subtype.val : (B.comap f).toLocalSubring.toSubring → K) hv
    simpa using this
  have hBunit : IsUnit ((f.comp A.subtype).codRestrict B.toSubring hmem a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨f (v : K), v.2⟩, ?_⟩
    apply Subtype.ext
    change f (a : K) * f (v : K) = 1
    rw [← map_mul, hval, map_one]
  exact hloc.map_nonunit a hBunit

end Domination

end ValuationSubring

namespace AlgebraicGeometry

open IsLocalRing

/-- The data of a **valuation probe** for a morphism `h : T ⟶ P` centred at `z ∈ P`:
a valuation ring `R` with fraction field `K`, a generic lift `η : Spec K ⟶ T`, and a
map `α : Spec R ⟶ P` forming a commutative square with `h` and taking the closed
point of `Spec R` to `z`.
(Blueprint: `def:nagata-dense-valuation-probe`.) -/
structure ValuationProbe {T P : Scheme.{u}} (h : T ⟶ P) (z : P) where
  /-- The valuation ring of the probe. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the probe. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The generic lift through the source. -/
  η : Spec (CommRingCat.of K) ⟶ T
  /-- The centred valuation map to the target. -/
  α : Spec (CommRingCat.of R) ⟶ P
  commSq : CommSq η (Spec.map (CommRingCat.ofHom (algebraMap R K))) h α
  closedPoint_eq : α (IsLocalRing.closedPoint R) = z

namespace ValuationProbe

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuationProbe

/-- **A point in the closure of the range of a quasi-compact morphism to an affine
scheme is a specialization of a point of the range** (the topological core of Stacks
Project Tag 02JQ): the point corresponds to a prime containing the kernel of one of
finitely many affine chart maps; a minimal prime of that kernel inside it lifts to
the chart (Stacks Tag 00FK), and the lifted point maps to a generization. -/
theorem exists_specializes_of_mem_closure_range {T P : Scheme.{u}} (h : T ⟶ P)
    [QuasiCompact h] [IsAffine P] {z : P} (hz : z ∈ closure (Set.range h)) :
    ∃ t : T, h t ⤳ z := by
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace h
  -- a finite affine cover of `T`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : T.affineOpens ↦ (V.1 : Set T)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : T.Opens) := trivial
      rw [← iSup_affineOpens_eq_top T] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- `z` lies in the closure of the image of one chart
  have hcover : Set.range h = ⋃ V ∈ s, h '' (V.1 : Set T) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact Set.mem_iUnion₂.mpr ⟨V, hVs, x, hxV, rfl⟩
    · rintro hy
      obtain ⟨V, -, x, -, rfl⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨x, rfl⟩
  rw [hcover, s.closure_biUnion] at hz
  obtain ⟨V₀, -, hzV₀⟩ := Set.mem_iUnion₂.mp hz
  -- the chart morphism, as a morphism of affine schemes
  set g : Spec Γ(T, V₀.1) ⟶ P := V₀.2.fromSpec ≫ h with hgdef
  have hrangeg : Set.range g = h '' (V₀.1 : Set T) := by
    rw [hgdef]
    have : ⇑(V₀.2.fromSpec ≫ h) = ⇑h ∘ ⇑V₀.2.fromSpec := by
      simp [Scheme.Hom.comp_base]
    rw [this, Set.range_comp, V₀.2.range_fromSpec]
  -- the chart morphism is induced by a ring map
  set φ : Γ(P, ⊤) ⟶ Γ(T, V₀.1) := g.appTop ≫ (Scheme.ΓSpecIso Γ(T, V₀.1)).hom with hφdef
  have hgSpec : g ≫ P.isoSpec.hom = Spec.map φ := by
    rw [← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, hφdef]
  -- transport `z` to the prime spectrum
  set z' := P.isoSpec.hom z with hz'def
  have him : P.isoSpec.hom '' (h '' (V₀.1 : Set T)) = Set.range (Spec.map φ) := by
    rw [← hrangeg, ← hgSpec]
    have : ⇑(g ≫ P.isoSpec.hom) = ⇑P.isoSpec.hom ∘ ⇑g := by
      simp [Scheme.Hom.comp_base]
    rw [this, Set.range_comp]
  have hz2 : z' ∈ closure (Set.range (Spec.map φ)) := by
    rw [← him]
    exact image_closure_subset_closure_image P.isoSpec.hom.continuous ⟨z, hzV₀, rfl⟩
  -- the prime of `z'` contains the kernel of `φ`
  have hkerle : RingHom.ker φ.hom ≤ z'.asIdeal := by
    have h1 : closure (Set.range (Spec.map φ)) =
        PrimeSpectrum.zeroLocus (RingHom.ker φ.hom : Set Γ(P, ⊤)) :=
      PrimeSpectrum.closure_range_comap φ.hom
    rw [h1] at hz2
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hz2
  -- choose a minimal prime of the kernel below `z'` and lift it to the chart
  haveI := z'.2
  obtain ⟨p₀, hp₀min, hp₀le⟩ := Ideal.exists_minimalPrimes_le hkerle
  rw [RingHom.ker_eq_comap_bot] at hp₀min
  obtain ⟨q, hq_prime, -, hq_comap⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes φ.hom p₀ hp₀min
  rw [← RingHom.ker_eq_comap_bot] at hp₀min
  haveI := hq_prime
  refine ⟨V₀.2.fromSpec ⟨q, hq_prime⟩, ?_⟩
  -- the lifted point maps to `p₀` in the spectrum
  have hgq : P.isoSpec.hom (h (V₀.2.fromSpec ⟨q, hq_prime⟩)) =
      (⟨p₀, hp₀min.1.1⟩ : PrimeSpectrum Γ(P, ⊤)) := by
    have h1 : P.isoSpec.hom (h (V₀.2.fromSpec ⟨q, hq_prime⟩)) =
        (g ≫ P.isoSpec.hom) ⟨q, hq_prime⟩ := by
      rw [hgdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [h1, hgSpec]
    exact PrimeSpectrum.ext hq_comap
  -- conclude by transporting the specialization `p₀ ⤳ z'` back along the isomorphism
  have hsp : (⟨p₀, hp₀min.1.1⟩ : PrimeSpectrum Γ(P, ⊤)) ⤳ z' :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hp₀le
  have hinv : ∀ w : P, P.isoSpec.inv (P.isoSpec.hom w) = w := by
    intro w
    rw [← Scheme.Hom.comp_apply, P.isoSpec.hom_inv_id]
    simp
  have := hsp.map P.isoSpec.inv.continuous
  rw [← hgq, hinv, hz'def, hinv] at this
  exact this

/-- **Existence of a valuation probe through a schematically dense source** (Stacks
Project Tag 02JQ): let `h : T ⟶ P` be quasi-compact and quasi-separated with trivial
kernel ideal sheaf (i.e. its scheme-theoretic image is all of `P`), with `P` affine,
and let `z ∈ P`. Then there is a valuation probe for `h` centred at `z`.

The proof combines `exists_specializes_of_mem_closure_range` (the range of `h` is
dense because the kernel vanishes, so `z` is a specialization of some `h t`) with the
stalk construction of Mathlib's valuative criterion: the composite
`𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` factors through a valuation subring `A ⊆ κ(t)` by
Chevalley extension (`IsLocalRing.exists_factor_valuationRing`), and the induced maps
`Spec κ(t) ⟶ T` and `Spec A ⟶ Spec 𝒪_{P,z} ⟶ P` form the probe.
(Blueprint: `lemma:nagata-dense-valuation-probe-exists`; proof order item 38.) -/
theorem exists_valuationRing_through_schemeDense_raw
    {T P : Scheme.{u}} (h : T ⟶ P) [QuasiCompact h] [QuasiSeparated h] [IsAffine P]
    (hker : h.ker = ⊥) (z : P) :
    Nonempty (ValuationProbe h z) := by
  haveI : IsSchemeTheoreticallyDominant h := ⟨hker⟩
  have hz : z ∈ closure (Set.range h) := by
    rw [h.denseRange.closure_range]
    trivial
  obtain ⟨t, ht⟩ := exists_specializes_of_mem_closure_range h hz
  -- the stalk composite `𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` and its valuation factorization
  let ρ : P.presheaf.stalk z ⟶ T.residueField t :=
    P.presheaf.stalkSpecializes ht ≫ h.stalkMap t ≫ T.residue t
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing ρ.hom
  let toA : P.presheaf.stalk z ⟶ .of A := CommRingCat.ofHom (ρ.hom.codRestrict _ hA)
  have w : T.fromSpecResidueField t ≫ h =
      Spec.map (CommRingCat.ofHom (algebraMap A (T.residueField t))) ≫
        Spec.map toA ≫ P.fromSpecStalk z := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ht]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨{ R := A
            K := T.residueField t
            η := T.fromSpecResidueField t
            α := Spec.map toA ≫ P.fromSpecStalk z
            commSq := ⟨w⟩
            closedPoint_eq := ?_ }⟩
  have h1 : Spec.map toA (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (P.presheaf.stalk z) :=
    IsLocalRing.comap_closedPoint (S := A) (ρ.hom.codRestrict A.toSubring hA)
  rw [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint]

namespace ValuativeCriterion

/-- **The dense-source valuative criterion, universal closedness** (Stacks Project
Tag 0894): let `f : X ⟶ S` be quasi-compact and let `h : U ⟶ X` be quasi-compact,
quasi-separated with dense range. If every valuative commutative square for `f`
whose generic point factors through `U` admits a unique lift, then `f` is universally
closed.

The Stacks Project proof reduces an arbitrary valuative square to one through `U` by
the valuation probe (`exists_valuationRing_through_schemeDense_raw`) applied to a
flat polynomial presentation of the generic point, the composite valuation ring
(`ValuationSubring.comapResidue`), the dominating extension
(`ValuationSubring.exists_dominating_extension`) and the intersection lemma
(`ValuationSubring.comap_eq_of_le_comap`).
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem universallyClosed_of_dense {U X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h] (hdense : Dense (Set.range h))
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    UniversallyClosed f := by
  sorry

/-- **The dense-source valuative criterion, separatedness** (Stacks Project Tag 0894):
under the hypotheses of `universallyClosed_of_dense`, if `f` is moreover
quasi-separated then it is separated: the uniqueness hypothesis makes the diagonal
satisfy the dense-source criterion for universal closedness, and a universally closed
immersion is a closed immersion.
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem isSeparated_of_dense {U X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (hdense : Dense (Set.range h))
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    IsSeparated f := by
  sorry

end ValuativeCriterion

end AlgebraicGeometry
