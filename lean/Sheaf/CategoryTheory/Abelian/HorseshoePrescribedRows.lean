/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Extending a fixed initial horseshoe embedding to a complex

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the cokernel induction to objects with prescribed outer resolutions.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.InjectiveResolution

/-- Choose the off-diagonal entries of the horseshoe differential. First descend
`-lift ≫ d_A` through the epimorphism `S.g`, and extend through the mono `IC.ι.f 0`.
Thereafter use exactness of `IC` and injectivity of the next term of `IA` to extend
`-δ n ≫ d_A`. Consecutive pairs retain their common entry under the recursion. -/
private theorem exists_twisting
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃)
    (lift : S.X₂ ⟶ IA.cocomplex.X 0) (hlift : S.f ≫ lift = IA.ι.f 0) :
    ∃ δ : ∀ n : ℕ, IC.cocomplex.X n ⟶ IA.cocomplex.X (n + 1),
      lift ≫ IA.cocomplex.d 0 1 + S.g ≫ IC.ι.f 0 ≫ δ 0 = 0 ∧
      ∀ n, δ n ≫ IA.cocomplex.d (n + 1) (n + 2) +
        IC.cocomplex.d n (n + 1) ≫ δ (n + 1) = 0 := by
  classical
  have := hS.epi_g
  have hq : S.f ≫ (-(lift ≫ IA.cocomplex.d 0 1)) = 0 := by
    simp [← Category.assoc, hlift]
  let q := hS.exact.desc (-(lift ≫ IA.cocomplex.d 0 1)) hq
  have hqfac : S.g ≫ q = -(lift ≫ IA.cocomplex.d 0 1) := hS.exact.g_desc _ _
  let a₀ := Injective.factorThru q (IC.ι.f 0)
  have ha₀ : IC.ι.f 0 ≫ a₀ = q := Injective.comp_factorThru _ _
  have hqzero : q ≫ IA.cocomplex.d 1 2 = 0 := by
    apply (cancel_epi S.g).1
    rw [← Category.assoc, hqfac]
    simp [Preadditive.neg_comp, Category.assoc]
  have hb₀ : IC.ι.f 0 ≫ (-(a₀ ≫ IA.cocomplex.d 1 2)) = 0 := by
    simp [Preadditive.comp_neg, ← Category.assoc, ha₀, hqzero]
  let b₀ := IC.exact₀.descToInjective (-(a₀ ≫ IA.cocomplex.d 1 2)) hb₀
  have hab₀ : a₀ ≫ IA.cocomplex.d 1 2 + IC.cocomplex.d 0 1 ≫ b₀ = 0 := by
    have h := IC.exact₀.comp_descToInjective (-(a₀ ≫ IA.cocomplex.d 1 2)) hb₀
    change IC.cocomplex.d 0 1 ≫ b₀ = -(a₀ ≫ IA.cocomplex.d 1 2) at h
    rw [h, add_neg_cancel]
  let F (n : ℕ) := Σ' (a : IC.cocomplex.X n ⟶ IA.cocomplex.X (n + 1))
      (b : IC.cocomplex.X (n + 1) ⟶ IA.cocomplex.X (n + 2)),
      a ≫ IA.cocomplex.d (n + 1) (n + 2) + IC.cocomplex.d n (n + 1) ≫ b = 0
  have next (n : ℕ) (p : F n) :
      ∃ c : IC.cocomplex.X (n + 2) ⟶ IA.cocomplex.X (n + 3),
        p.2.1 ≫ IA.cocomplex.d (n + 2) (n + 3) +
          IC.cocomplex.d (n + 1) (n + 2) ≫ c = 0 := by
    have hp : IC.cocomplex.d n (n + 1) ≫
        (p.2.1 ≫ IA.cocomplex.d (n + 2) (n + 3)) = 0 := by
      have h := congrArg (fun f ↦ f ≫ IA.cocomplex.d (n + 2) (n + 3)) p.2.2
      simpa [Preadditive.add_comp, Category.assoc] using h
    have hp' : IC.cocomplex.d n (n + 1) ≫
        (-(p.2.1 ≫ IA.cocomplex.d (n + 2) (n + 3))) = 0 := by
      simp [Preadditive.comp_neg, hp]
    refine ⟨(IC.exact_succ n).descToInjective _ hp', ?_⟩
    have h := (IC.exact_succ n).comp_descToInjective _ hp'
    change IC.cocomplex.d (n + 1) (n + 2) ≫ _ =
      -(p.2.1 ≫ IA.cocomplex.d (n + 2) (n + 3)) at h
    rw [h, add_neg_cancel]
  let step (n : ℕ) (p : F n) : F (n + 1) :=
    ⟨p.2.1, (next n p).choose, (next n p).choose_spec⟩
  let seq : ∀ n, F n := Nat.rec ⟨a₀, b₀, hab₀⟩ step
  refine ⟨fun n ↦ (seq n).1, ?_, ?_⟩
  · change lift ≫ IA.cocomplex.d 0 1 + S.g ≫ IC.ι.f 0 ≫ a₀ = 0
    rw [ha₀, hqfac, add_neg_cancel]
  · intro n
    change (seq n).1 ≫ IA.cocomplex.d (n + 1) (n + 2) +
      IC.cocomplex.d n (n + 1) ≫ (seq n).2.1 = 0
    exact (seq n).2.2

/-- Extend a chosen initial horseshoe embedding to compatible augmented complexes
with short exact rows. This only constructs a complex: positive-degree exactness,
injectivity of its terms, and the quasi-isomorphism of its augmentation are not
part of the conclusion and are verified separately.

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the following cokernel induction to prescribed resolutions of objects.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).

Proof: put `K.X 0 = IA.X 0 ⊞ IC.X 0` and augment by
`w = (lift, S.g ≫ IC.ι.f 0)`. The hypothesis on `lift` gives a morphism from
`S` to the split biproduct row. Its outer vertical maps are monomorphisms,
so the snake lemma makes `w` a monomorphism and gives a short exact sequence
of the three cokernels. For either outer resolution, exactness identifies the
cokernel of its augmentation with a subobject of its degree-one term. Use
these two embeddings at the next step. Extend the left embedding across the
monomorphism of the cokernel sequence into the injective left degree-one term;
pair this extension with the right embedding composed with the quotient map.
This gives the middle embedding into the degree-one biproduct. Apply the
snake lemma again to obtain the next short exact sequence of cokernels.
Continue recursively, always using the embeddings supplied by exactness of
the prescribed outer resolutions into their next injective terms.

Define each middle differential as the quotient map onto the current middle
cokernel followed by its new embedding. Consecutive differentials compose to
zero because the quotient kills the preceding embedding. The squares defining
the induced cokernel maps, followed by the embedding squares, show that the
biproduct inclusions and projections commute with differentials; hence they
assemble into `α` and `β`. Their composite is zero degreewise. The degree-zero
squares give the augmentation equalities. Each row is the canonical split
biproduct row. The identity in degree zero gives `e₀` and its equation.
Finally, the first middle differential factors through the cokernel of `w`
followed by a monomorphism, so its kernel is the image of `w`; this is the
asserted degree-zero exactness. The augmentation is the complex map determined
by `w`, which is killed by the first differential. -/
theorem exists_horseshoe_prescribed_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃)
    (lift : S.X₂ ⟶ IA.cocomplex.X 0) (hlift : S.f ≫ lift = IA.ι.f 0) :
    ∃ (K : CochainComplex C ℕ)
      (ι : (CochainComplex.single₀ C).obj S.X₂ ⟶ K)
      (α : IA.cocomplex ⟶ K) (β : K ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ ι ∧
      ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      (∃ e₀ : K.X 0 ≅ IA.cocomplex.X 0 ⊞ IC.cocomplex.X 0,
        ι.f 0 ≫ e₀.hom = biprod.lift lift (S.g ≫ IC.ι.f 0)) ∧
      (ShortComplex.mk (ι.f 0) (K.d 0 1) (by simp)).Exact ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact := by
  classical
  -- Use triangular differentials instead of the cokernel induction in the original plan.
  obtain ⟨δ, hδ₀, hδ⟩ := exists_twisting S hS IA IC lift hlift
  let X (n : ℕ) := IA.cocomplex.X n ⊞ IC.cocomplex.X n
  let d (n : ℕ) : X n ⟶ X (n + 1) :=
    biprod.lift (biprod.fst ≫ IA.cocomplex.d n (n + 1) + biprod.snd ≫ δ n)
      (biprod.snd ≫ IC.cocomplex.d n (n + 1))
  have hd (n : ℕ) : d n ≫ d (n + 1) = 0 := by
    apply biprod.hom_ext <;> apply biprod.hom_ext'
    all_goals simp [d, Category.assoc, Preadditive.comp_add, Preadditive.add_comp, hδ]
  let K : CochainComplex C ℕ := CochainComplex.of X d hd
  let α : IA.cocomplex ⟶ K := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro n
    apply biprod.hom_ext <;> simp [K, d, Category.assoc, Preadditive.comp_add])
  let β : K ⟶ IC.cocomplex := CochainComplex.ofHom (fun _ ↦ biprod.snd) (by
    intro n
    simp [K, d])
  let w : S.X₂ ⟶ X 0 := biprod.lift lift (S.g ≫ IC.ι.f 0)
  have hw : w ≫ K.d 0 1 = 0 := by
    change w ≫ CochainComplex.of.d X d 0 (0 + 1) = 0
    rw [CochainComplex.of_d]
    apply biprod.hom_ext
    · simpa [K, d, w, Category.assoc, Preadditive.comp_add] using hδ₀
    · simp [d, w, Category.assoc]
  let ι := (CochainComplex.fromSingle₀Equiv K S.X₂).symm ⟨w, hw⟩
  have hι : ι.f 0 = w := by simp [ι]
  have hα : IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ ι := by
    apply HomologicalComplex.from_single_hom_ext
    apply biprod.hom_ext <;> simp [α, hι, w, Category.assoc, hlift, S.zero_assoc]
  have hβ : ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι := by
    apply HomologicalComplex.from_single_hom_ext
    simp [β, hι, w]
  have hαβ : α ≫ β = 0 := by ext n; simp [α, β]
  refine ⟨K, ι, α, β, hα, hβ, ⟨Iso.refl _, ?_⟩, ?_, hαβ, ?_⟩
  · simpa using hι
  · -- Lift a cycle's right coordinate, subtract its augmented lift, then lift the left.
    have := hS.epi_g
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    change T ⟶ X 0 at x
    change x ≫ K.d 0 1 = 0 at hx
    change ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (b : T' ⟶ S.X₂),
      π ≫ x = b ≫ ι.f 0
    have hKd : K.d 0 1 = d 0 := CochainComplex.of_d X d 0
    have hc : (x ≫ biprod.snd) ≫ IC.cocomplex.d 0 1 = 0 := by
      have h := congrArg (fun f ↦ f ≫ biprod.snd) hx
      simpa [hKd, d, Category.assoc] using h
    let c : T ⟶ S.X₃ := IC.exact₀.lift (x ≫ biprod.snd) hc
    have hclift : c ≫ IC.ι.f 0 = x ≫ biprod.snd := IC.exact₀.lift_f _ _
    obtain ⟨T', π, hπ, b, hb⟩ := surjective_up_to_refinements_of_epi S.g c
    let y : T' ⟶ X 0 := π ≫ x - b ≫ w
    have hysnd : y ≫ biprod.snd = 0 := by
      simp only [y, Preadditive.sub_comp, Category.assoc, w, biprod.lift_snd]
      rw [← Category.assoc b S.g _, ← hb, Category.assoc, hclift, sub_self]
    have hyd : y ≫ d 0 = 0 := by
      have hx' : x ≫ d 0 = 0 := by simpa [hKd] using hx
      have hw' : w ≫ d 0 = 0 := by simpa [hKd] using hw
      simp [y, Preadditive.sub_comp, Category.assoc, hx', hw']
    have ha : (y ≫ biprod.fst) ≫ IA.cocomplex.d 0 1 = 0 := by
      have h := congrArg (fun f ↦ f ≫ biprod.fst) hyd
      simpa [d, Category.assoc, Preadditive.comp_add,
        ← Category.assoc y biprod.snd, hysnd] using h
    let a : T' ⟶ S.X₁ := IA.exact₀.lift (y ≫ biprod.fst) ha
    have halift : a ≫ IA.ι.f 0 = y ≫ biprod.fst := IA.exact₀.lift_f _ _
    refine ⟨T', π, hπ, a ≫ S.f + b, ?_⟩
    simp only [hι]
    apply biprod.hom_ext
    · simp only [Category.assoc, w, biprod.lift_fst, Preadditive.add_comp,
        hlift, halift]
      simp [y, w, Preadditive.sub_comp, Category.assoc]
    · simp only [Category.assoc, w, biprod.lift_snd, Preadditive.add_comp,
        S.zero_assoc, comp_zero, zero_comp, zero_add]
      rw [← Category.assoc b S.g _, ← hb, Category.assoc, hclift]
  · intro n
    change (ShortComplex.mk biprod.inl biprod.snd _).ShortExact
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct
      (IA.cocomplex.X n) (IC.cocomplex.X n)).shortExact

end CategoryTheory.InjectiveResolution
