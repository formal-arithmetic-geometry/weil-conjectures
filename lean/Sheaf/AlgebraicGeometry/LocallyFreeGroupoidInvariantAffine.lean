/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.DescentNormLocusAffine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Invariant affine shrinking for a finite locally free groupoid

Source: Stacks Project, Groupoids, Tag 03JE, `lemma-find-invariant-affine`
(blueprint: lem-sfb-locally-free-groupoid-invariant-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Prime avoidance chooses one principal open around a finite set in an affine open. -/
private theorem finite_subset_basicOpen
    {X : Scheme.{u}} (A : X.Opens) (hA : IsAffineOpen A)
    (S : Set X) (hS : S.Finite) (x : X) (hx : x ∈ S)
    (B : X.Opens) (hSB : S ⊆ (B : Set X)) (hBA : B ≤ A) :
    ∃ f : Γ(X, A), S ⊆ (X.basicOpen f : Set X) ∧ X.basicOpen f ≤ B := by
  classical
  let J : Ideal Γ(X, A) :=
    { carrier := {f | X.basicOpen f ≤ B}
      zero_mem' := by simp
      add_mem' := fun hf hg ↦ (X.basicOpen_add_le _ _).trans (sup_le hf hg)
      smul_mem' := fun a f hf ↦ by
        change X.basicOpen (a * f) ≤ B
        rw [X.basicOpen_mul]
        exact inf_le_right.trans hf }
  let T : Set (PrimeSpectrum Γ(X, A)) := hA.fromSpec ⁻¹' S
  have hT : T.Finite := hS.preimage hA.fromSpec.isOpenEmbedding.injective.injOn
  obtain ⟨p, hp⟩ : x ∈ Set.range hA.fromSpec := by
    rw [hA.range_fromSpec]
    exact hBA (hSB hx)
  have hnot : ¬ ∃ q ∈ T, J ≤ q.asIdeal := by
    rintro ⟨q, hq, hJq⟩
    obtain ⟨f, hfB, hqf⟩ := hA.exists_basicOpen_le
      ⟨hA.fromSpec q, hSB hq⟩ (hBA (hSB hq))
    have hmem : f ∉ q.asIdeal := by
      change q ∈ PrimeSpectrum.basicOpen f
      rw [← hA.fromSpec_preimage_basicOpen]
      exact hqf
    exact hmem (hJq hfB)
  have hnot' : ¬ (J : Set Γ(X, A)) ⊆ ⋃ q ∈ T, (q.asIdeal : Set Γ(X, A)) := by
    rw [Ideal.subset_union_prime_finite hT p p (fun q _ _ _ ↦ q.isPrime)]
    exact hnot
  obtain ⟨f, hfJ, hf⟩ := Set.not_subset.mp hnot'
  refine ⟨f, ?_, hfJ⟩
  intro y hy
  obtain ⟨q, rfl⟩ : y ∈ Set.range hA.fromSpec := by
    rw [hA.range_fromSpec]
    exact hBA (hSB hy)
  change q ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen f
  rw [hA.fromSpec_preimage_basicOpen]
  intro hfq
  exact hf (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hy, hfq⟩⟩)

/-- An orbit contained in an affine open has an invariant affine open neighbourhood.
Source: Stacks Project, Groupoids, Tag 03JE, `lemma-find-invariant-affine`
(blueprint: lem-sfb-locally-free-groupoid-invariant-affine).

Proof:
1. For each y, put O(y) = t(s⁻¹({y})). The identity and inversion give reflexivity
   and symmetry. To compose arrows over an underlying middle point, embed their
   residue fields in a common extension using `lem-weil-common-extension-fields`.
   The laws of `def-a1-groupoid-scheme` then give transitivity, hence equal orbits
   for the endpoints of any arrow. Finite fibres of s, by
   `lem-weil-pbc-finite-closed-map-finite-fibres`, make O(x) finite; it contains x.
2. For an open E, set H(E) = U minus t(s⁻¹(U minus E)). The same finite-map lemma
   makes this open. Inversion identifies membership with O(y) contained in E.
   Thus H(E) is invariant and contained in E, and contains O(x) whenever E does.
   Choose an affine open A containing O(x), and set B = H(A).
3. Write A as the spectrum of its section ring using `def-pc-scheme` and
   `def-weil-affine-spectrum`. The basic-open basis from
   `lem-weil-pbc-spec-localization-away-basic-open` supplies functions with basic
   opens contained in B, nonvanishing at each point of O(x). Their generated ideal
   is not contained in any of the finitely many orbit primes. Prime avoidance
   (`lem-weil-pbc-prime-avoidance`) gives f with O(x) contained in D(f) contained in B.
4. Set W = H(D(f)). Then W is invariant, contains O(x), and is contained in D(f).
   Inversion exchanges the t-image of an s-preimage with the s-image of a
   t-preimage. Hence W is B intersected with the complement of
   s(t⁻¹(U minus D(f))).
5. Apply `lem-pd-descent-norm-locus-affine` with ambient scheme U, affine A,
   intermediate open B, section f, and output W. Invariance of B gives
   s⁻¹(B) contained in t⁻¹(A); the other hypotheses are steps 3 and 4.
   Its determinant norm is formed on B and restricted to the affine D(f), so W
   is affine. No affineness of B, constant degree, Noetherian, separatedness or
   dimension assumption is needed. Equality of inverse-image opens gives equality
   of the corresponding open subschemes of R. -/
theorem exists_invariant_affine_of_finiteLocallyFree_groupoid
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (_hG : IsGroupoidScheme s t e i c)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] (x : U)
    (hx : ∃ A : U.Opens, IsAffineOpen A ∧ t '' (s ⁻¹' {x}) ⊆ (A : Set U)) :
    ∃ W : U.Opens, IsAffineOpen W ∧ t '' (s ⁻¹' {x}) ⊆ (W : Set U) ∧
      s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  classical
  let rel : U → U → Prop := fun a b ↦ ∃ r : R, s r = a ∧ t r = b
  have hrefl (y : U) : rel y y := by
    refine ⟨e y, ?_, ?_⟩
    · exact congrArg (fun f : U ⟶ U ↦ f y) _hG.identity_source
    · exact congrArg (fun f : U ⟶ U ↦ f y) _hG.identity_target
  have hsymm {a b : U} : rel a b → rel b a := by
    rintro ⟨r, hr, ht⟩
    refine ⟨i r, ?_, ?_⟩
    · exact (congrArg (fun f : R ⟶ U ↦ f r) _hG.inverse_source).trans ht
    · exact (congrArg (fun f : R ⟶ U ↦ f r) _hG.inverse_target).trans hr
  have htrans {a b d : U} : rel a b → rel b d → rel a d := by
    rintro ⟨r₁, hs₁, ht₁⟩ ⟨r₂, hs₂, ht₂⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := s) (g := t) r₂ r₁ (hs₂.trans ht₁.symm)
    refine ⟨c z, ?_, ?_⟩
    · have h := congrArg (fun f : pullback s t ⟶ U ↦ f z) _hG.composition_source
      simpa only [Scheme.Hom.comp_apply, hz₂, hs₁] using h
    · have h := congrArg (fun f : pullback s t ⟶ U ↦ f z) _hG.composition_target
      simpa only [Scheme.Hom.comp_apply, hz₁, ht₂] using h
  let H : U.Opens → U.Opens := fun E ↦
    ⟨(s '' (t ⁻¹' (E : Set U)ᶜ))ᶜ,
      (s.isClosedMap _ (E.isOpen.isClosed_compl.preimage t.continuous)).isOpen_compl⟩
  have hH (E : U.Opens) (y : U) : y ∈ H E ↔ ∀ z, rel y z → z ∈ E := by
    constructor
    · intro hy z hz
      obtain ⟨r, hr, rfl⟩ := hz
      by_contra ht
      exact hy ⟨r, ht, hr⟩
    · intro hy
      rintro ⟨r, hr, he⟩
      exact hr (hy (t r) ⟨r, he, rfl⟩)
  have hHle (E : U.Opens) : H E ≤ E := by
    intro y hy
    exact (hH E y).mp hy y (hrefl y)
  have hHinv (E : U.Opens) : s ⁻¹ᵁ H E = t ⁻¹ᵁ H E := by
    ext r
    change s r ∈ H E ↔ t r ∈ H E
    rw [hH, hH]
    have hr : rel (s r) (t r) := ⟨r, rfl, rfl⟩
    exact ⟨fun h z hz ↦ h z (htrans hr hz),
      fun h z hz ↦ h z (htrans (hsymm hr) hz)⟩
  have hHcontains (E : U.Opens)
      (hE : t '' (s ⁻¹' {x}) ⊆ (E : Set U)) :
      t '' (s ⁻¹' {x}) ⊆ (H E : Set U) := by
    rintro y ⟨r, hr, rfl⟩
    apply (hH E (t r)).mpr
    intro z hz
    obtain ⟨q, hqx, hqz⟩ := htrans ⟨r, hr, rfl⟩ hz
    exact hE ⟨q, hqx, hqz⟩
  obtain ⟨A, hA, hOA⟩ := hx
  let B := H A
  have hOB : t '' (s ⁻¹' {x}) ⊆ (B : Set U) := hHcontains A hOA
  have hxO : x ∈ t '' (s ⁻¹' {x}) := by
    obtain ⟨r, hr, ht⟩ := hrefl x
    exact ⟨r, hr, ht⟩
  obtain ⟨f, hOf, hfB⟩ := finite_subset_basicOpen A hA _
    ((s.finite_preimage_singleton x).image t) x hxO B hOB (hHle A)
  let W := H (U.basicOpen f)
  have hOW : t '' (s ⁻¹' {x}) ⊆ (W : Set U) := hHcontains _ hOf
  have hWf : W ≤ U.basicOpen f := hHle _
  have hWB : W ≤ B := hWf.trans hfB
  refine ⟨W, ?_, hOW, hHinv _⟩
  have hBAarrow : s ⁻¹' (B : Set U) ⊆ t ⁻¹' (A : Set U) := by
    intro r hr
    have htB : t r ∈ B := by
      have hinv := hHinv A
      exact (SetLike.ext_iff.mp hinv r).mp hr
    exact hHle A htB
  apply CategoryTheory.Over.DescentDatum.isAffineOpen_descent_norm_locus
    s t A hA B hBAarrow f hfB W hWf
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨hWB hy, hy⟩
  · exact fun _ hy ↦ hy.2

end AlgebraicGeometry
