/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# The dense-source valuative criterion

This file provides the scheme-theoretic inputs of the two-open compactification
theorem, following the blueprint chapter "Nagata compactification", section
"The dense-source valuative criterion" (proof order items 38–42):

- `AlgebraicGeometry.ValuationProbe` and `AlgebraicGeometry.nonempty_valuationProbe`:
  the **valuation probe through a schematically dense source** (Stacks Project
  Tag 02JQ; blueprint: `lemma:nagata-dense-valuation-probe-exists`; proof order
  item 38);
- `AlgebraicGeometry.ValuativeCriterion.universallyClosed_of_isDominant` and
  `AlgebraicGeometry.ValuativeCriterion.isSeparated_of_isDominant`: the
  **dense-source valuative criterion** (Stacks Project Tag 0894; blueprint:
  `lemma:nagata-dense-source-valuative`; proof order item 42): unique valuation
  lifting against squares whose generic point passes through a dense source implies
  universal closedness, and separatedness when the morphism is quasi-separated.

The valuation-theoretic inputs (proof order items 39–41) live in the Mathlib helper
files:

- the **composite of two valuation rings** `ValuationSubring.comapResidue` (blueprint:
  `lemma:nagata-composite-valuation-ring`; item 39) in
  `WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring`;
- the **intersection with a dominating valuation ring**
  `ValuationSubring.comap_eq_of_le_comap` (Stacks Tag 052K; blueprint:
  `lemma:nagata-valuation-intersection`; item 40) and the **extension of a valuation
  ring to a field extension** `ValuationSubring.exists_comap_eq` (Stacks Tag 00IA;
  blueprint: `lemma:nagata-valuation-ring-extension`; item 41) in
  `WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`;
- the topological core of the probe,
  `AlgebraicGeometry.exists_specializes_of_mem_closure_range`, in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

The proof of the dense-source valuative
criterion (item 42, Stacks Tag 0894) reduces an arbitrary valuative square to one
through the dense source. Two reductions differ from the Stacks Project text: instead
of replacing the schemes by their reductions, `h` is factored through its
scheme-theoretic image (`Scheme.Hom.toImage` is scheme-theoretically dominant with no
reducedness hypothesis, and morphisms from reduced affine schemes factor through the
image by `Scheme.IdealSheafData.le_ker_of_range_subset_support`); and the base is
localized to an affine chart through which the valuation-ring leg of the square
factors. The remaining core (`existence_core`) follows the Stacks Project: the
valuation probe (item 38) applied to a flat polynomial presentation of the generic
point, the composite valuation ring (item 39), the extension lemma (item 41) and the
intersection lemma (item 40).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

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

/-- **Existence of a valuation probe through a schematically dense source** (Stacks
Project Tag 02JQ): let `h : T ⟶ P` be quasi-compact and scheme-theoretically
dominant, with `P` affine, and let `z ∈ P`. Then there is a valuation probe for `h`
centred at `z`.

The proof combines `exists_specializes_of_mem_closure_range` (the range of `h` is
dense, so `z` is a specialization of some `h t`) with the stalk construction of
Mathlib's valuative criterion: the composite `𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` factors
through a valuation subring `A ⊆ κ(t)` by Chevalley extension
(`IsLocalRing.exists_factor_valuationRing`), and the induced maps `Spec κ(t) ⟶ T`
and `Spec A ⟶ Spec 𝒪_{P,z} ⟶ P` form the probe.
(Blueprint: `lemma:nagata-dense-valuation-probe-exists`; proof order item 38.) -/
theorem nonempty_valuationProbe {T P : Scheme.{u}} (h : T ⟶ P) [QuasiCompact h]
    [IsSchemeTheoreticallyDominant h] [IsAffine P] (z : P) :
    Nonempty (ValuationProbe h z) := by
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

section ExistenceCore

/-- The image of a valuation ring in its fraction field, as a valuation subring. -/
private def fractionValuationSubring (A K : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] : ValuationSubring K :=
  ValuationSubring.ofSubring (algebraMap A K).range fun x ↦
    (ValuationRing.isInteger_or_isInteger A x).imp (fun h ↦ h) fun h ↦ h

/-- A valuation ring is isomorphic to its image in its fraction field. -/
private def fractionValuationSubringEquiv (A K : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    A ≃+* fractionValuationSubring A K :=
  RingEquiv.ofBijective ((algebraMap A K).rangeRestrict)
    ⟨fun _ _ hab ↦ IsFractionRing.injective A K (Subtype.ext_iff.mp hab),
      (algebraMap A K).rangeRestrict_surjective⟩

private lemma algebraMap_fractionValuationSubringEquiv (A K : Type u) [CommRing A]
    [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] (a : A) :
    algebraMap (fractionValuationSubring A K) K (fractionValuationSubringEquiv A K a) =
      algebraMap A K a :=
  rfl

private lemma algebraMap_fractionValuationSubringEquiv_symm (A K : Type u) [CommRing A]
    [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (v : fractionValuationSubring A K) :
    algebraMap A K ((fractionValuationSubringEquiv A K).symm v) = (v : K) := by
  rw [← algebraMap_fractionValuationSubringEquiv A K, RingEquiv.apply_symm_apply,
    ValuationSubring.algebraMap_apply]

/-- Morphisms from the spectrum of a domain to an affine scheme are determined by their
restriction to the generic point: `Spec` of the inclusion into the fraction field is an
epimorphism of schemes onto its source in this weak sense. -/
private lemma eq_of_specMap_algebraMap_comp_eq {R : CommRingCat.{u}} {A K : Type u}
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {a b : Spec (CommRingCat.of A) ⟶ Spec R}
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b) : a = b := by
  have : Mono (CommRingCat.ofHom (algebraMap A K)) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
      (IsFractionRing.injective A K)
  have h1 : Spec.preimage a ≫ CommRingCat.ofHom (algebraMap A K) =
      Spec.preimage b ≫ CommRingCat.ofHom (algebraMap A K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact h
  rw [← Spec.map_preimage a, ← Spec.map_preimage b, (cancel_mono _).mp h1]

/-- **A flat presentation of a field-valued point** (Steps 1 and 2 of the Stacks
Project proof of Tag 0894): every morphism `i₁ : Spec K ⟶ X` from the spectrum of a
field factors as `Spec K ⟶ Spec P ⟶ X` with `P ↠ K` surjective and `Spec P ⟶ X`
flat. For `P` one takes a polynomial ring, with one variable for every element of `K`,
over the sections of an affine chart around the image point. -/
private lemma exists_flat_presentation_of_field_point {X : Scheme.{u}} {K : Type u}
    [Field K] (i₁ : Spec (CommRingCat.of K) ⟶ X) :
    ∃ (P : CommRingCat.{u}) (π : P ⟶ CommRingCat.of K) (p : Spec P ⟶ X),
      Function.Surjective π.hom ∧ Flat p ∧ Spec.map π ≫ p = i₁ := by
  -- an affine chart `V` around the image of the `K`-point
  obtain ⟨V, hV, hx₀V⟩ : ∃ V : X.Opens, IsAffineOpen V ∧
      i₁ (closedPoint (CommRingCat.of K)) ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx₀V, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i₁ (closedPoint (CommRingCat.of K)))) isOpen_univ
    exact ⟨V, hV, hx₀V⟩
  have hrange : Set.range i₁ ⊆ (V : Set X) := by
    rintro - ⟨y, rfl⟩
    have hy : y = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
    rw [hy]
    exact hx₀V
  let j : Spec (CommRingCat.of K) ⟶ V := IsOpenImmersion.lift V.ι i₁
    (by rwa [Scheme.Opens.range_ι])
  have hj : j ≫ V.ι = i₁ := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, V) ⟶ CommRingCat.of K := Spec.preimage (j ≫ hV.isoSpec.hom)
  have hφ : Spec.map φ ≫ hV.isoSpec.inv ≫ V.ι = i₁ := by
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, hj]
  -- the polynomial ring with one variable for every element of `K`
  let P : Type u := MvPolynomial K ↥Γ(X, V)
  let π : P →+* K := MvPolynomial.eval₂Hom φ.hom id
  have hπ : Function.Surjective π := fun k ↦ ⟨MvPolynomial.X k, MvPolynomial.eval₂Hom_X' _ _ _⟩
  let p : Spec (CommRingCat.of P) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, V) P)) ≫ hV.isoSpec.inv ≫ V.ι
  have hpflat : Flat p := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, V) P))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    infer_instance
  have hpdef : p = Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, V) P)) ≫
      hV.isoSpec.inv ≫ V.ι := rfl
  have hπC : π.comp (algebraMap ↥Γ(X, V) P) = φ.hom := MvPolynomial.eval₂Hom_comp_C _ _
  have hi₁p : Spec.map (CommRingCat.ofHom π) ≫ p = i₁ := by
    rw [hpdef, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hπC,
      CommRingCat.ofHom_hom, hφ]
  exact ⟨CommRingCat.of P, CommRingCat.ofHom π, p, hπ, hpflat, hi₁p⟩

open IsLocalRing in
/-- The heart of the dense-source valuative criterion (Stacks Project Tag 0894), for an
affine base and a scheme-theoretically dominant source: given the unique-lifting
hypothesis against squares through `U`, every valuative square for `f` has a lift. -/
private lemma existence_core {U X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (h : U ⟶ X) [QuasiCompact h] [IsSchemeTheoreticallyDominant h]
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂)
    (sq : ValuativeCommSq f) : sq.commSq.HasLift := by
  obtain ⟨A, K, i₁, i₂, ⟨w⟩⟩ := sq
  letI : Field (CommRingCat.of K) := ‹_›
  obtain ⟨P, π, p, hπ, hpflat, hi₁p⟩ := exists_flat_presentation_of_field_point i₁
  -- Step 3: the valuation probe through `U ×_X Spec P ⟶ Spec P`.
  have : QuasiCompact (pullback.snd h p) := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨pr⟩ := nonempty_valuationProbe (pullback.snd h p)
    (Spec.map π (closedPoint (CommRingCat.of K)))
  -- Step 4: replace the abstract probe valuation ring by its image in `pr.K`.
  let VA' : ValuationSubring pr.K := fractionValuationSubring pr.R pr.K
  let e' : pr.R ≃+* ↥VA' := fractionValuationSubringEquiv pr.R pr.K
  have : IsLocalHom (e' : pr.R →+* ↥VA') := ⟨fun a ha ↦ by
    simpa using ha.map e'.symm.toRingHom⟩
  let αV : Spec (CommRingCat.of ↥VA') ⟶ Spec P :=
    Spec.map (CommRingCat.ofHom (e' : pr.R →+* ↥VA')) ≫ pr.α
  have halg : CommRingCat.ofHom (e' : pr.R →+* ↥VA') ≫
      CommRingCat.ofHom (algebraMap ↥VA' pr.K) =
      CommRingCat.ofHom (algebraMap pr.R pr.K) := by
    ext a
    rfl
  have hαVdef : αV = Spec.map (CommRingCat.ofHom (e' : pr.R →+* ↥VA')) ≫ pr.α := rfl
  have hprobe : pr.η ≫ pullback.snd h p =
      Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫ αV := by
    rw [pr.commSq.w, hαVdef, ← Category.assoc, ← Spec.map_comp, halg]
  have he'closed : (Spec.map (CommRingCat.ofHom (e' : pr.R →+* ↥VA'))) (closedPoint ↥VA') =
      closedPoint pr.R := IsLocalRing.comap_closedPoint _
  have hclosed : αV (closedPoint ↥VA') =
      Spec.map π (closedPoint (CommRingCat.of K)) := by
    rw [hαVdef, Scheme.Hom.comp_apply, he'closed, pr.closedPoint_eq]
  -- Step 5: descend the residue map of `VA'` to a field embedding `τ : K → k'`.
  let ρ : P ⟶ CommRingCat.of ↥VA' := Spec.preimage αV
  have hρ : Spec.map ρ = αV := Spec.map_preimage _
  have hker : ∀ a ∈ RingHom.ker π.hom, ρ.hom a ∈ maximalIdeal ↥VA' := by
    intro a ha
    have hmem : Spec.map π (closedPoint (CommRingCat.of K)) ∈
        PrimeSpectrum.zeroLocus {a} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      refine Ideal.mem_comap.mpr ?_
      rw [RingHom.mem_ker] at ha
      rw [ha]
      exact zero_mem _
    rw [← hclosed, ← hρ, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
    exact hmem
  obtain ⟨τ, hτπ⟩ :=
    IsLocalRing.exists_ringHom_residue_comp_of_surjective hπ ρ.hom hker
  -- Step 6: extend the valuation ring `A ⊆ K` along `τ` and form the composite.
  let VA : ValuationSubring K := fractionValuationSubring A K
  obtain ⟨A'', hA''⟩ := ValuationSubring.exists_comap_eq τ VA
  let C : ValuationSubring pr.K := VA'.comapResidue A''
  have hCA' : C.toSubring ≤ VA'.toSubring := VA'.comapResidue_le A''
  let ιC : ↥C →+* ↥VA' := Subring.inclusion hCA'
  -- Step 7: the square through `U` for the composite valuation ring `C`.
  let ψ : R ⟶ CommRingCat.of A := Spec.preimage i₂
  have hψ : Spec.map ψ = i₂ := Spec.map_preimage _
  let pre : R ⟶ P := Spec.preimage (p ≫ f)
  have hpre : Spec.map pre = p ≫ f := Spec.map_preimage _
  let θ : ↥R →+* ↥VA' := ρ.hom.comp pre.hom
  have hπpre : pre ≫ π = ψ ≫ CommRingCat.ofHom (algebraMap A K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hpre, hψ, ← Category.assoc, hi₁p, w]
  have hθmem : ∀ r : ↥R, residue ↥VA' (θ r) ∈ A'' := by
    intro r
    have h2 : residue ↥VA' (θ r) = τ (π.hom (pre.hom r)) := by
      have h1 : τ (π.hom (pre.hom r)) = τ.comp π.hom (pre.hom r) := rfl
      rw [h1, hτπ]
      rfl
    have h3 : π.hom (pre.hom r) = algebraMap A K (ψ.hom r) :=
      congrArg (fun (g : R ⟶ CommRingCat.of K) ↦ g.hom r) hπpre
    have h4 : algebraMap A K (ψ.hom r) ∈ VA := ⟨ψ.hom r, rfl⟩
    rw [← hA''] at h4
    rwa [h2, h3]
  let γ : ↥R →+* ↥C := ((algebraMap ↥VA' pr.K).comp θ).codRestrict C.toSubring
    (fun r ↦ (VA'.mem_comapResidue A'').mpr ⟨(θ r).2, hθmem r⟩)
  -- the two basic compatibilities of `γ` and `θ` at the level of `Spec`
  have hγθ : Spec.map (CommRingCat.ofHom (algebraMap ↥C pr.K)) ≫
      Spec.map (CommRingCat.ofHom γ) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫
        Spec.map (CommRingCat.ofHom θ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
  have hθdef : CommRingCat.ofHom θ = pre ≫ ρ := rfl
  have hθspec : Spec.map (CommRingCat.ofHom θ) = αV ≫ (p ≫ f) := by
    rw [hθdef, Spec.map_comp, hρ, hpre]
  have hηθ : Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫
      Spec.map (CommRingCat.ofHom θ) = (pr.η ≫ pullback.fst h p ≫ h) ≫ f := by
    rw [hθspec, ← reassoc_of% hprobe, ← pullback.condition_assoc]
    simp only [Category.assoc]
  have hsqC : (pr.η ≫ pullback.fst h p ≫ h) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ↥C pr.K)) ≫
        Spec.map (CommRingCat.ofHom γ) := by
    rw [hγθ, hηθ]
  let sqC : ValuativeCommSq f :=
    { R := ↥C
      K := pr.K
      i₁ := pr.η ≫ pullback.fst h p ≫ h
      i₂ := Spec.map (CommRingCat.ofHom γ)
      commSq := ⟨hsqC⟩ }
  obtain ⟨gC, ⟨hgC1, hgC2⟩, -⟩ := H sqC (pr.η ≫ pullback.fst h p) (Category.assoc _ _ _)
  -- Step 8: uniqueness applied over `VA'` identifies the two maps `Spec VA' ⟶ X`.
  let sq' : ValuativeCommSq f :=
    { R := ↥VA'
      K := pr.K
      i₁ := pr.η ≫ pullback.fst h p ≫ h
      i₂ := αV ≫ p ≫ f
      commSq := ⟨by rw [← hηθ, hθspec]⟩ }
  obtain ⟨l', -, hl'uniq⟩ := H sq' (pr.η ≫ pullback.fst h p) (Category.assoc _ _ _)
  have hE : Spec.map (CommRingCat.ofHom ιC) ≫ gC = αV ≫ p := by
    have h1 : αV ≫ p = l' := hl'uniq (αV ≫ p) ⟨by
        rw [← Category.assoc, ← hprobe, Category.assoc, ← pullback.condition], rfl⟩
    have hιCalg : (algebraMap ↥VA' pr.K).comp ιC = algebraMap ↥C pr.K := rfl
    have hsqCi₂ : sqC.i₂ = Spec.map (CommRingCat.ofHom γ) := rfl
    have hιCγ : ιC.comp γ = θ := by
      ext r
      rfl
    have h2 : Spec.map (CommRingCat.ofHom ιC) ≫ gC = l' := by
      refine hl'uniq _ ⟨?_, ?_⟩
      · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιCalg]
        exact hgC1
      · rw [Category.assoc, hgC2, hsqCi₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          hιCγ, hθspec]
    rw [h2, ← h1]
  -- Step 9: restrict `gC` along the closed immersion `Spec A'' ⟶ Spec C`.
  have : ValuationRing ↥A''.toSubring := inferInstanceAs (ValuationRing ↥A'')
  have : IsDomain ↥A''.toSubring := inferInstanceAs (IsDomain ↥A'')
  have : IsLocalRing ↥A''.toSubring := inferInstanceAs (IsLocalRing ↥A'')
  let rr : ↥C →+* ↥A''.toSubring := VA'.residueRestrict A''
  let g'' : Spec (CommRingCat.of ↥A''.toSubring) ⟶ X := Spec.map (CommRingCat.ofHom rr) ≫ gC
  -- Identity (I): the generic point of `Spec A''` recovers the base change of `i₁`
  -- along `τ`.
  have hcomm : ρ ≫ CommRingCat.ofHom (residue ↥VA') =
      π ≫ CommRingCat.ofHom τ := by
    apply CommRingCat.hom_ext
    simpa using hτπ.symm
  have hg''def : g'' = Spec.map (CommRingCat.ofHom rr) ≫ gC := rfl
  have hsubrr : (A''.toSubring.subtype).comp rr = (residue ↥VA').comp ιC := rfl
  have hI : Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫ g'' =
      Spec.map (CommRingCat.ofHom τ) ≫ i₁ := by
    rw [hg''def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsubrr,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hE,
      ← hρ, ← Category.assoc, ← Spec.map_comp, hcomm, Spec.map_comp, Category.assoc,
      hi₁p]
  -- From here on, only the established equations matter: make the constructed data
  -- opaque so that unification does not unfold it.
  clear_value rr g'' γ θ pre ψ ρ αV e' VA'
  -- The closed point of `Spec A''` maps to a specialization of the `K`-point.
  have hτlocal : IsLocalHom τ := ⟨fun a ha ↦ by
    by_contra hna
    rw [isUnit_iff_ne_zero, not_not] at hna
    rw [hna, map_zero] at ha
    exact ha.ne_zero rfl⟩
  have : IsLocalHom (CommRingCat.ofHom τ).hom := hτlocal
  have hgen : g'' ((Spec.map (CommRingCat.ofHom A''.toSubring.subtype))
      (closedPoint (ResidueField ↥VA'))) = i₁ (closedPoint (CommRingCat.of K)) :=
    calc g'' ((Spec.map (CommRingCat.ofHom A''.toSubring.subtype))
          (closedPoint (ResidueField ↥VA')))
        = (Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫ g'')
            (closedPoint (ResidueField ↥VA')) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom τ) ≫ i₁) (closedPoint (ResidueField ↥VA')) := by
          rw [hI]
      _ = i₁ ((Spec.map (CommRingCat.ofHom τ)) (closedPoint (ResidueField ↥VA'))) :=
          Scheme.Hom.comp_apply _ _ _
      _ = i₁ (closedPoint (CommRingCat.of K)) := congrArg (fun q ↦ i₁ q) Spec_closedPoint
  have hspec : i₁ (closedPoint (CommRingCat.of K)) ⤳ g'' (closedPoint ↥A''.toSubring) := by
    rw [← hgen]
    exact (specializes_closedPoint _).map g''.continuous
  -- The stalk map of `i₁` at the closed point, transported along the specialization.
  let κ : X.presheaf.stalk (g'' (closedPoint ↥A''.toSubring)) ⟶ CommRingCat.of K :=
    X.presheaf.stalkSpecializes hspec ≫ Scheme.stalkClosedPointTo i₁
  have hκSpec : Spec.map κ ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) = i₁ :=
    calc Spec.map κ ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))
        = (Spec.map (Scheme.stalkClosedPointTo i₁) ≫
              Spec.map (X.presheaf.stalkSpecializes hspec)) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          congrArg (· ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)))
            (Spec.map_comp _ _)
      _ = Spec.map (Scheme.stalkClosedPointTo i₁) ≫
            (Spec.map (X.presheaf.stalkSpecializes hspec) ≫
              X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) := Category.assoc _ _ _
      _ = Spec.map (Scheme.stalkClosedPointTo i₁) ≫
            X.fromSpecStalk (i₁ (closedPoint (CommRingCat.of K))) :=
          congrArg (Spec.map (Scheme.stalkClosedPointTo i₁) ≫ ·)
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hspec)
      _ = i₁ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk i₁
  clear_value κ
  -- The master identity: `τ ∘ κ` is the closed-point stalk map of `g''`.
  have hpre : IsPreimmersion (X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) :=
    inferInstance
  have hMspec : Spec.map (κ ≫ CommRingCat.ofHom τ) ≫
        X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) =
      Spec.map (Scheme.stalkClosedPointTo g'' ≫ CommRingCat.ofHom A''.toSubring.subtype) ≫
        X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
    calc Spec.map (κ ≫ CommRingCat.ofHom τ) ≫
          X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))
        = (Spec.map (CommRingCat.ofHom τ) ≫ Spec.map κ) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          congrArg (· ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)))
            (Spec.map_comp _ _)
      _ = Spec.map (CommRingCat.ofHom τ) ≫
            (Spec.map κ ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom τ) ≫ i₁ :=
          congrArg (Spec.map (CommRingCat.ofHom τ) ≫ ·) hκSpec
      _ = Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫ g'' := hI.symm
      _ = Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫
            (Spec.map (Scheme.stalkClosedPointTo g'') ≫
              X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) :=
          congrArg (Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫ ·)
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g'').symm
      _ = (Spec.map (CommRingCat.ofHom A''.toSubring.subtype) ≫
              Spec.map (Scheme.stalkClosedPointTo g'')) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          (Category.assoc _ _ _).symm
      _ = Spec.map (Scheme.stalkClosedPointTo g'' ≫ CommRingCat.ofHom A''.toSubring.subtype) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          congrArg (· ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)))
            (Spec.map_comp _ _).symm
  have hM : κ ≫ CommRingCat.ofHom τ =
      Scheme.stalkClosedPointTo g'' ≫ CommRingCat.ofHom A''.toSubring.subtype :=
    Spec.map_injective ((cancel_mono _).mp hMspec)
  -- Hence the image of `κ` lies in `A = K ∩ A''`.
  have hκmem : ∀ s, κ.hom s ∈ VA := by
    intro s
    have h1 : τ (κ.hom s) =
        A''.toSubring.subtype ((Scheme.stalkClosedPointTo g'').hom s) := by
      have h2 := congrArg (fun (g : X.presheaf.stalk
        (g'' (closedPoint ↥A''.toSubring)) ⟶ CommRingCat.of (ResidueField ↥VA')) ↦
          g.hom s) hM
      simpa using h2
    rw [← hA'']
    change τ (κ.hom s) ∈ A''
    rw [h1]
    exact ((Scheme.stalkClosedPointTo g'').hom s).2
  -- Assemble the lift `Spec A ⟶ X` from the corestricted stalk map.
  let φl : X.presheaf.stalk (g'' (closedPoint ↥A''.toSubring)) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((fractionValuationSubringEquiv A K).symm.toRingHom.comp
      (κ.hom.codRestrict VA.toSubring hκmem))
  have hφκ : φl ≫ CommRingCat.ofHom (algebraMap A K) = κ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun s ↦ ?_
    change algebraMap A K ((fractionValuationSubringEquiv A K).symm ⟨κ.hom s, hκmem s⟩) =
      κ.hom s
    exact algebraMap_fractionValuationSubringEquiv_symm A K ⟨κ.hom s, hκmem s⟩
  -- The lift and its two compatibilities. The generic one comes from `hκSpec`; the
  -- base one follows by comparing the corresponding ring maps into `R` after
  -- embedding `A` into `K`.
  have hl1 : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
      (Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) = i₁ :=
    calc Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
          (Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)))
        = (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ Spec.map φl) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) := (Category.assoc _ _ _).symm
      _ = Spec.map (φl ≫ CommRingCat.ofHom (algebraMap A K)) ≫
            X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          congrArg (· ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)))
            (Spec.map_comp _ _).symm
      _ = Spec.map κ ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)) :=
          congrArg (Spec.map · ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) hφκ
      _ = i₁ := hκSpec
  have hl2 : (Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring))) ≫ f =
      i₂ := by
    refine eq_of_specMap_algebraMap_comp_eq (A := A) (K := K) ?_
    rw [← Category.assoc, hl1, w]
  exact ⟨⟨⟨Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''.toSubring)), hl1, hl2⟩⟩⟩

end ExistenceCore

/-- **The dense-source valuative criterion, universal closedness** (Stacks Project
Tag 0894): let `f : X ⟶ S` be quasi-compact and let `h : U ⟶ X` be quasi-compact,
quasi-separated and dominant. If every valuative commutative square for `f` whose
generic point factors through `U` admits a unique lift, then `f` is universally
closed.

The proof reduces an arbitrary valuative square to one through `U`. First `h` is
factored through its scheme-theoretic image — the factor map `h.toImage` is
scheme-theoretically dominant, and the valuative data factors through the image by
`Scheme.IdealSheafData.le_ker_of_range_subset_support` since spectra of valuation
rings and fields are reduced — and the base is localized to an affine chart through
which the valuation-ring leg factors. The core (`existence_core`) then follows the
Stacks Project: the valuation probe (`nonempty_valuationProbe`) applied to a flat
polynomial presentation of the generic point, the composite valuation ring
(`ValuationSubring.comapResidue`), the extension lemma
(`ValuationSubring.exists_comap_eq`) and the intersection lemma
(`ValuationSubring.comap_eq_of_le_comap`).
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem universallyClosed_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h] [IsDominant h]
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    UniversallyClosed f := by
  apply UniversallyClosed.of_valuativeCriterion
  rintro ⟨A, K, i₁, i₂, ⟨w⟩⟩
  letI : Field (CommRingCat.of K) := ‹_›
  -- The factor map through the scheme-theoretic image is scheme-theoretically
  -- dominant: its kernel vanishes on the affine cover of the image pulled back from
  -- `X`, where the section map is injective by `Scheme.Hom.toImage_app_injective`.
  have : IsSchemeTheoreticallyDominant h.toImage := by
    refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : X.affineOpens ↦ ⟨h.imageι ⁻¹ᵁ U.1, U.2.preimage h.imageι⟩)
      (h.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)) fun U ↦ ?_⟩
    simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (h.toImage_app_injective U)
  -- Since `h` is dominant, the scheme-theoretic image of `h` is topologically all of
  -- `X`, so every morphism from a reduced scheme factors through it.
  have hsupp : (h.ker.support : Set X) = Set.univ := by
    rw [Scheme.Hom.support_ker h]
    simpa using h.denseRange.closure_range
  have hfac : ∀ {Z : Scheme.{u}} (l : Z ⟶ X) [IsReduced Z], h.imageι.ker ≤ l.ker := by
    intro Z l hZ
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact h.ker.le_ker_of_range_subset_support l (by rw [hsupp]; exact Set.subset_univ _)
  let i₁' : Spec (CommRingCat.of K) ⟶ h.image :=
    IsClosedImmersion.lift h.imageι i₁ (hfac i₁)
  have hi₁' : i₁' ≫ h.imageι = i₁ := IsClosedImmersion.lift_fac _ _ _
  -- An affine chart of `S` through which `i₂` factors.
  obtain ⟨VS, hVS, hi₂VS⟩ : ∃ VS : S.Opens, IsAffineOpen VS ∧
      i₂ (closedPoint (CommRingCat.of A)) ∈ VS := by
    obtain ⟨_, ⟨VS, hVS, rfl⟩, hx, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i₂ (closedPoint (CommRingCat.of A)))) isOpen_univ
    exact ⟨VS, hVS, hx⟩
  have hrange₂ : Set.range i₂ ⊆ (VS : Set S) := by
    rintro - ⟨y, rfl⟩
    exact ((specializes_closedPoint y).map i₂.continuous).mem_open VS.2 hi₂VS
  let i₂' : Spec (CommRingCat.of A) ⟶ VS := IsOpenImmersion.lift VS.ι i₂
    (by rwa [Scheme.Opens.range_ι])
  have hi₂' : i₂' ≫ VS.ι = i₂ := IsOpenImmersion.lift_fac _ _ _
  -- Restrict the image factorization over the chart; the restricted source stays
  -- quasi-compact and scheme-theoretically dominant.
  let W₂ : h.image.Opens := (h.imageι ≫ f) ⁻¹ᵁ VS
  have : QuasiCompact (h.toImage ∣_ W₂) :=
    IsZariskiLocalAtTarget.restrict (P := @QuasiCompact) inferInstance W₂
  have : IsSchemeTheoreticallyDominant (h.toImage ∣_ W₂) :=
    .of_isPullback (isPullback_morphismRestrict h.toImage W₂).flip
  have hWU : (h.toImage ∣_ W₂) ≫ W₂.ι = (h.toImage ⁻¹ᵁ W₂).ι ≫ h.toImage :=
    morphismRestrict_ι _ _
  let f₂ : W₂.toScheme ⟶ Spec Γ(S, VS) := ((h.imageι ≫ f) ∣_ VS) ≫ hVS.isoSpec.hom
  have hf₂ι : f₂ ≫ hVS.isoSpec.inv ≫ VS.ι = W₂.ι ≫ h.imageι ≫ f := by
    change (((h.imageι ≫ f) ∣_ VS) ≫ hVS.isoSpec.hom) ≫ hVS.isoSpec.inv ≫ VS.ι = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
  -- The unique-lifting hypothesis descends to the restricted data.
  have H₂ : ∀ (sq₂ : ValuativeCommSq f₂)
      (ηU₂ : Spec (CommRingCat.of sq₂.K) ⟶ (h.toImage ⁻¹ᵁ W₂).toScheme),
      ηU₂ ≫ (h.toImage ∣_ W₂) = sq₂.i₁ →
      ∃! l : Spec (CommRingCat.of sq₂.R) ⟶ W₂.toScheme,
        Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ l = sq₂.i₁ ∧
        l ≫ f₂ = sq₂.i₂ := by
    intro sq₂ ηU₂ hηU₂
    have hcommX : (sq₂.i₁ ≫ W₂.ι ≫ h.imageι) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫
          (sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι) :=
      calc (sq₂.i₁ ≫ W₂.ι ≫ h.imageι) ≫ f
          = sq₂.i₁ ≫ W₂.ι ≫ h.imageι ≫ f := by simp only [Category.assoc]
        _ = sq₂.i₁ ≫ f₂ ≫ hVS.isoSpec.inv ≫ VS.ι :=
            congrArg (sq₂.i₁ ≫ ·) hf₂ι.symm
        _ = (sq₂.i₁ ≫ f₂) ≫ hVS.isoSpec.inv ≫ VS.ι := (Category.assoc _ _ _).symm
        _ = (Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ sq₂.i₂) ≫
              hVS.isoSpec.inv ≫ VS.ι :=
            congrArg (· ≫ hVS.isoSpec.inv ≫ VS.ι) sq₂.commSq.w
        _ = Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫
              (sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι) := Category.assoc _ _ _
    let sqX : ValuativeCommSq f :=
      { R := sq₂.R
        K := sq₂.K
        i₁ := sq₂.i₁ ≫ W₂.ι ≫ h.imageι
        i₂ := sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι
        commSq := ⟨hcommX⟩ }
    have hηUX : (ηU₂ ≫ (h.toImage ⁻¹ᵁ W₂).ι) ≫ h = sqX.i₁ :=
      calc (ηU₂ ≫ (h.toImage ⁻¹ᵁ W₂).ι) ≫ h
          = (ηU₂ ≫ (h.toImage ⁻¹ᵁ W₂).ι) ≫ h.toImage ≫ h.imageι :=
            congrArg ((ηU₂ ≫ (h.toImage ⁻¹ᵁ W₂).ι) ≫ ·) (Scheme.Hom.toImage_imageι h).symm
        _ = (ηU₂ ≫ (h.toImage ∣_ W₂) ≫ W₂.ι) ≫ h.imageι := by
            rw [hWU]
            simp only [Category.assoc]
        _ = sq₂.i₁ ≫ W₂.ι ≫ h.imageι := by
            rw [← Category.assoc, ← Category.assoc, hηU₂, Category.assoc]
    obtain ⟨lX, ⟨hlX1, hlX2⟩, hlXuniq⟩ := H sqX (ηU₂ ≫ (h.toImage ⁻¹ᵁ W₂).ι) hηUX
    let l₁ : Spec (CommRingCat.of sq₂.R) ⟶ h.image :=
      IsClosedImmersion.lift h.imageι lX (hfac lX)
    have hl₁ : l₁ ≫ h.imageι = lX := IsClosedImmersion.lift_fac _ _ _
    have hl₁f : l₁ ≫ h.imageι ≫ f = sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι :=
      calc l₁ ≫ h.imageι ≫ f = (l₁ ≫ h.imageι) ≫ f := (Category.assoc _ _ _).symm
        _ = lX ≫ f := congrArg (· ≫ f) hl₁
        _ = sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι := hlX2
    have hrangel₁ : Set.range l₁ ⊆ (W₂ : Set h.image) := by
      rintro - ⟨y, rfl⟩
      change (h.imageι ≫ f) (l₁ y) ∈ VS
      have h7 : (h.imageι ≫ f) (l₁ y) =
          (hVS.isoSpec.inv ≫ VS.ι) ((sq₂.i₂) y) :=
        calc (h.imageι ≫ f) (l₁ y)
            = (l₁ ≫ h.imageι ≫ f) y := (Scheme.Hom.comp_apply _ _ _).symm
          _ = (sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι) y := by rw [hl₁f]
          _ = (hVS.isoSpec.inv ≫ VS.ι) ((sq₂.i₂) y) := Scheme.Hom.comp_apply _ _ _
      rw [h7, Scheme.Hom.comp_apply]
      have h10 : VS.ι ((hVS.isoSpec.inv) ((sq₂.i₂) y)) ∈ Set.range VS.ι :=
        Set.mem_range_self _
      rwa [Scheme.Opens.range_ι] at h10
    let l₂ : Spec (CommRingCat.of sq₂.R) ⟶ W₂.toScheme :=
      IsOpenImmersion.lift W₂.ι l₁ (by rwa [Scheme.Opens.range_ι])
    have hl₂ : l₂ ≫ W₂.ι = l₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨l₂, ⟨?_, ?_⟩, ?_⟩
    · refine (cancel_mono (W₂.ι ≫ h.imageι)).mp ?_
      calc (Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ l₂) ≫
            W₂.ι ≫ h.imageι
          = Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫
              (l₂ ≫ W₂.ι) ≫ h.imageι := by simp only [Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ l₁ ≫ h.imageι := by
            rw [hl₂]
        _ = Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ lX := by rw [hl₁]
        _ = sq₂.i₁ ≫ W₂.ι ≫ h.imageι := hlX1
    · have h9 : l₂ ≫ ((h.imageι ≫ f) ∣_ VS) = sq₂.i₂ ≫ hVS.isoSpec.inv := by
        refine (cancel_mono VS.ι).mp ?_
        calc (l₂ ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ VS.ι
            = l₂ ≫ ((h.imageι ≫ f) ∣_ VS) ≫ VS.ι := Category.assoc _ _ _
          _ = l₂ ≫ W₂.ι ≫ h.imageι ≫ f := by rw [morphismRestrict_ι]
          _ = (l₂ ≫ W₂.ι) ≫ h.imageι ≫ f := (Category.assoc _ _ _).symm
          _ = l₁ ≫ h.imageι ≫ f := congrArg (· ≫ h.imageι ≫ f) hl₂
          _ = sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι := hl₁f
          _ = (sq₂.i₂ ≫ hVS.isoSpec.inv) ≫ VS.ι := (Category.assoc _ _ _).symm
      calc l₂ ≫ f₂
          = (l₂ ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ hVS.isoSpec.hom := (Category.assoc _ _ _).symm
        _ = (sq₂.i₂ ≫ hVS.isoSpec.inv) ≫ hVS.isoSpec.hom :=
            congrArg (· ≫ hVS.isoSpec.hom) h9
        _ = sq₂.i₂ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · intro y hy
      have h5 : y ≫ ((h.imageι ≫ f) ∣_ VS) = sq₂.i₂ ≫ hVS.isoSpec.inv :=
        calc y ≫ ((h.imageι ≫ f) ∣_ VS)
            = (y ≫ (((h.imageι ≫ f) ∣_ VS) ≫ hVS.isoSpec.hom)) ≫ hVS.isoSpec.inv := by
              simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
          _ = sq₂.i₂ ≫ hVS.isoSpec.inv := congrArg (· ≫ hVS.isoSpec.inv) hy.2
      have hyX : y ≫ W₂.ι ≫ h.imageι = lX := by
        refine hlXuniq _ ⟨?_, ?_⟩
        · calc Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫
                y ≫ W₂.ι ≫ h.imageι
              = (Spec.map (CommRingCat.ofHom (algebraMap sq₂.R sq₂.K)) ≫ y) ≫
                  W₂.ι ≫ h.imageι := (Category.assoc _ _ _).symm
            _ = sq₂.i₁ ≫ W₂.ι ≫ h.imageι := congrArg (· ≫ W₂.ι ≫ h.imageι) hy.1
        · calc (y ≫ W₂.ι ≫ h.imageι) ≫ f
              = y ≫ W₂.ι ≫ h.imageι ≫ f := by simp only [Category.assoc]
            _ = y ≫ ((h.imageι ≫ f) ∣_ VS) ≫ VS.ι := by rw [morphismRestrict_ι]
            _ = (y ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ VS.ι := (Category.assoc _ _ _).symm
            _ = (sq₂.i₂ ≫ hVS.isoSpec.inv) ≫ VS.ι := congrArg (· ≫ VS.ι) h5
            _ = sq₂.i₂ ≫ hVS.isoSpec.inv ≫ VS.ι := Category.assoc _ _ _
      refine (cancel_mono (W₂.ι ≫ h.imageι)).mp ?_
      calc y ≫ W₂.ι ≫ h.imageι
          = lX := hyX
        _ = l₁ ≫ h.imageι := hl₁.symm
        _ = (l₂ ≫ W₂.ι) ≫ h.imageι := congrArg (· ≫ h.imageι) hl₂.symm
        _ = l₂ ≫ W₂.ι ≫ h.imageι := Category.assoc _ _ _
  -- The original square restricts to a square for `f₂` through the restricted source.
  have h6 : i₁' ≫ h.imageι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂ :=
    calc i₁' ≫ h.imageι ≫ f = (i₁' ≫ h.imageι) ≫ f := (Category.assoc _ _ _).symm
      _ = i₁ ≫ f := congrArg (· ≫ f) hi₁'
      _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂ := w
  have hrange₁' : Set.range i₁' ⊆ (W₂ : Set h.image) := by
    rintro - ⟨y, rfl⟩
    change (h.imageι ≫ f) (i₁' y) ∈ VS
    have h7 : (h.imageι ≫ f) (i₁' y) =
        i₂ ((Spec.map (CommRingCat.ofHom (algebraMap A K))) y) :=
      calc (h.imageι ≫ f) (i₁' y)
          = (i₁' ≫ h.imageι ≫ f) y := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂) y := by rw [h6]
        _ = i₂ ((Spec.map (CommRingCat.ofHom (algebraMap A K))) y) :=
            Scheme.Hom.comp_apply _ _ _
    rw [h7]
    exact hrange₂ (Set.mem_range_self _)
  let i₁'' : Spec (CommRingCat.of K) ⟶ W₂.toScheme :=
    IsOpenImmersion.lift W₂.ι i₁' (by rwa [Scheme.Opens.range_ι])
  have hi₁'' : i₁'' ≫ W₂.ι = i₁' := IsOpenImmersion.lift_fac _ _ _
  have hcomm₂ : i₁'' ≫ f₂ =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂' ≫ hVS.isoSpec.hom := by
    have h8 : i₁'' ≫ ((h.imageι ≫ f) ∣_ VS) =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂' := by
      refine (cancel_mono VS.ι).mp ?_
      calc (i₁'' ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ VS.ι
          = i₁'' ≫ ((h.imageι ≫ f) ∣_ VS) ≫ VS.ι := Category.assoc _ _ _
        _ = i₁'' ≫ W₂.ι ≫ h.imageι ≫ f := by rw [morphismRestrict_ι]
        _ = (i₁'' ≫ W₂.ι) ≫ h.imageι ≫ f := (Category.assoc _ _ _).symm
        _ = i₁' ≫ h.imageι ≫ f := congrArg (· ≫ h.imageι ≫ f) hi₁''
        _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂ := h6
        _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂' ≫ VS.ι := by rw [hi₂']
        _ = (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂') ≫ VS.ι :=
            (Category.assoc _ _ _).symm
    calc i₁'' ≫ f₂
        = (i₁'' ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ hVS.isoSpec.hom := (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂') ≫ hVS.isoSpec.hom :=
          congrArg (· ≫ hVS.isoSpec.hom) h8
      _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i₂' ≫ hVS.isoSpec.hom :=
          Category.assoc _ _ _
  obtain ⟨l₂, hlift1, hlift2⟩ := (existence_core f₂ (h.toImage ∣_ W₂) H₂
    { R := A
      K := K
      i₁ := i₁''
      i₂ := i₂' ≫ hVS.isoSpec.hom
      commSq := ⟨hcomm₂⟩ }).exists_lift
  -- Assemble the lift of the original square.
  have h9 : l₂ ≫ ((h.imageι ≫ f) ∣_ VS) = i₂' :=
    calc l₂ ≫ ((h.imageι ≫ f) ∣_ VS)
        = (l₂ ≫ (((h.imageι ≫ f) ∣_ VS) ≫ hVS.isoSpec.hom)) ≫ hVS.isoSpec.inv := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (i₂' ≫ hVS.isoSpec.hom) ≫ hVS.isoSpec.inv :=
          congrArg (· ≫ hVS.isoSpec.inv) hlift2
      _ = i₂' := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨⟨⟨l₂ ≫ W₂.ι ≫ h.imageι, ?_, ?_⟩⟩⟩
  · calc Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ l₂ ≫ W₂.ι ≫ h.imageι
        = (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ l₂) ≫ W₂.ι ≫ h.imageι :=
          (Category.assoc _ _ _).symm
      _ = i₁'' ≫ W₂.ι ≫ h.imageι := congrArg (· ≫ W₂.ι ≫ h.imageι) hlift1
      _ = (i₁'' ≫ W₂.ι) ≫ h.imageι := (Category.assoc _ _ _).symm
      _ = i₁' ≫ h.imageι := congrArg (· ≫ h.imageι) hi₁''
      _ = i₁ := hi₁'
  · calc (l₂ ≫ W₂.ι ≫ h.imageι) ≫ f
        = l₂ ≫ W₂.ι ≫ h.imageι ≫ f := by simp only [Category.assoc]
      _ = l₂ ≫ ((h.imageι ≫ f) ∣_ VS) ≫ VS.ι := by rw [morphismRestrict_ι]
      _ = (l₂ ≫ ((h.imageι ≫ f) ∣_ VS)) ≫ VS.ι := (Category.assoc _ _ _).symm
      _ = i₂' ≫ VS.ι := congrArg (· ≫ VS.ι) h9
      _ = i₂ := hi₂'

/-- **The dense-source valuative criterion, separatedness** (Stacks Project Tag 0894):
under the hypotheses of `universallyClosed_of_isDominant`, if `f` is moreover
quasi-separated then it is separated: the uniqueness hypothesis makes the diagonal
satisfy the dense-source criterion for universal closedness, and a universally closed
immersion is a closed immersion.
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem isSeparated_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h] [IsDominant h]
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    IsSeparated f := by
  constructor
  have : UniversallyClosed (pullback.diagonal f) := by
    refine universallyClosed_of_isDominant (pullback.diagonal f) h ?_
    intro sq ηU hηU
    -- A square for the diagonal is a pair of maps to `X` agreeing over `S`; the
    -- uniqueness hypothesis for `f` forces the pair to coincide.
    have hfst : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
        (sq.i₂ ≫ pullback.fst f f) = sq.i₁ :=
      calc Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
            (sq.i₂ ≫ pullback.fst f f)
          = (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂) ≫
              pullback.fst f f := (Category.assoc _ _ _).symm
        _ = (sq.i₁ ≫ pullback.diagonal f) ≫ pullback.fst f f :=
            congrArg (· ≫ pullback.fst f f) sq.commSq.w.symm
        _ = sq.i₁ ≫ pullback.diagonal f ≫ pullback.fst f f := Category.assoc _ _ _
        _ = sq.i₁ := by rw [pullback.diagonal_fst, Category.comp_id]
    have hsnd : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
        (sq.i₂ ≫ pullback.snd f f) = sq.i₁ :=
      calc Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
            (sq.i₂ ≫ pullback.snd f f)
          = (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂) ≫
              pullback.snd f f := (Category.assoc _ _ _).symm
        _ = (sq.i₁ ≫ pullback.diagonal f) ≫ pullback.snd f f :=
            congrArg (· ≫ pullback.snd f f) sq.commSq.w.symm
        _ = sq.i₁ ≫ pullback.diagonal f ≫ pullback.snd f f := Category.assoc _ _ _
        _ = sq.i₁ := by rw [pullback.diagonal_snd, Category.comp_id]
    have hcomm : sq.i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
        (sq.i₂ ≫ pullback.fst f f ≫ f) :=
      calc sq.i₁ ≫ f
          = (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
              (sq.i₂ ≫ pullback.fst f f)) ≫ f := congrArg (· ≫ f) hfst.symm
        _ = Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
              (sq.i₂ ≫ pullback.fst f f ≫ f) := by simp only [Category.assoc]
    obtain ⟨l₀, -, hl₀uniq⟩ := H
      { R := sq.R
        K := sq.K
        i₁ := sq.i₁
        i₂ := sq.i₂ ≫ pullback.fst f f ≫ f
        commSq := ⟨hcomm⟩ } ηU hηU
    have hfst' : sq.i₂ ≫ pullback.fst f f = l₀ :=
      hl₀uniq _ ⟨hfst, Category.assoc _ _ _⟩
    have hsnd' : sq.i₂ ≫ pullback.snd f f = l₀ := by
      refine hl₀uniq _ ⟨hsnd, ?_⟩
      calc (sq.i₂ ≫ pullback.snd f f) ≫ f
          = sq.i₂ ≫ pullback.snd f f ≫ f := Category.assoc _ _ _
        _ = sq.i₂ ≫ pullback.fst f f ≫ f := by rw [← pullback.condition]
    have heq : sq.i₂ ≫ pullback.fst f f = sq.i₂ ≫ pullback.snd f f :=
      hfst'.trans hsnd'.symm
    refine ⟨sq.i₂ ≫ pullback.fst f f, ⟨hfst, ?_⟩, ?_⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact heq
    · intro y hy
      calc y = y ≫ pullback.diagonal f ≫ pullback.fst f f := by
            rw [pullback.diagonal_fst, Category.comp_id]
        _ = (y ≫ pullback.diagonal f) ≫ pullback.fst f f := (Category.assoc _ _ _).symm
        _ = sq.i₂ ≫ pullback.fst f f := congrArg (· ≫ pullback.fst f f) hy.2
  exact IsClosedImmersion.of_isPreimmersion _
    (pullback.diagonal f).isClosedMap.isClosed_range

end ValuativeCriterion

end AlgebraicGeometry
