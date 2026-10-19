/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionData
import Sheaf.CategoryTheory.YonedaExtensionClass
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Existence of the geometric Baer construction

Source: Stacks Project, Homology Section 010I, Baer sum construction.
(blueprint: lem-coef-yoneda-baer-existence)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

set_option backward.isDefEq.respectTransparency false in
private theorem pushout_exact_pair {X Y Z W : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hz : f ≫ g = 0) (he : (ShortComplex.mk f g hz).Exact) [Mono f]
    (u : X ⟶ W) :
    (ShortComplex.mk (pushout.inl u f) (pushout.desc 0 g (by simp [hz]))
      (by simp)).Exact := by
  let S : ShortComplex A := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel f
      mono_f := inferInstance
      epi_g := inferInstance }
  obtain ⟨_, p, hp₀, hp₁, _, hP, _⟩ := pushout_short_exact_sequence S hS u
  change pushout.inl u f ≫ p = 0 at hp₀
  let k : cokernel f ⟶ Z := cokernel.desc f g hz
  have hk : Mono k := he.mono_cokernelDesc
  have hd : pushout.desc 0 g (by simp [S, hz]) = p ≫ k := by
    apply pushout.hom_ext
    · change pushout.inl u f ≫ pushout.desc 0 g _ = pushout.inl u f ≫ (p ≫ k)
      simp only [pushout.inl_desc, ← Category.assoc, hp₀, zero_comp]
    · simp [← Category.assoc, hp₁, S, k]
  let φ : ShortComplex.mk (pushout.inl u f) p hp₀ ⟶
      ShortComplex.mk (pushout.inl u f) (p ≫ k) (by simp [← Category.assoc, hp₀]) :=
    { τ₁ := 𝟙 W
      τ₂ := 𝟙 _
      τ₃ := k
      comm₁₂ := by simp
      comm₂₃ := by simp }
  let ψ : ShortComplex.mk (pushout.inl u f) (p ≫ k)
      (by simp [← Category.assoc, hp₀]) ⟶
      ShortComplex.mk (pushout.inl u f) (pushout.desc 0 g (by simp [hz]))
        (by simp) :=
    { τ₁ := 𝟙 W
      τ₂ := 𝟙 _
      τ₃ := 𝟙 Z
      comm₁₂ := by simp
      comm₂₃ := by simpa only [Category.id_comp, Category.comp_id] using hd }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hP.exact)

set_option backward.isDefEq.respectTransparency false in
/-- Push out the first injection of an extension along a map of left endpoints.
Source: Stacks Project, Homology Section 010I.
Proof: form the actual pushout; exactness follows from the short exact cokernel
head, and later exactness follows by epimorphic refinements.
(blueprint: lem-coef-yoneda-baer-existence) -/
theorem pushout_extension {V U W : A} (n : ℕ)
    (E : YonedaExtension A V U (n + 1)) (u : V ⟶ W) :
    ∃ (G : YonedaExtension A W U (n + 1)) (c : E.sequence ⟶ G.sequence),
      E.leftMap G c = u ∧ E.rightMap G c = 𝟙 U ∧
      IsPushout (E.leftIso.inv ≫ E.sequence.map' 0 1) u
        (c.app 1) (G.leftIso.inv ≫ G.sequence.map' 0 1) ∧
      ∀ k : Fin (n + 3), 1 < k.val → IsIso (c.app k) := by
  let j := E.leftIso.inv ≫ E.sequence.map' 0 1
  let g := E.sequence.map' 1 2
  have hj : Mono j := by
    have := E.first_mono
    dsimp [j]
    infer_instance
  have hz : j ≫ g = 0 := by
    simp [j, g, Category.assoc, E.exact.toIsComplex.zero 0]
  let S := ShortComplex.mk j g hz
  let φ : S ⟶ E.sequence.sc E.exact.toIsComplex 0 :=
    { τ₁ := E.leftIso.inv
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, j]
      comm₂₃ := by simp [S, g] }
  have he : S.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (E.exact.exact 0)
  let d : pushout u j ⟶ E.sequence.obj' 2 := pushout.desc 0 g (by simp [hz])
  let R := E.sequence.δ₀.δ₀.precomp d
  let T := R.precomp (pushout.inl u j)
  have hR : R.Exact := by
    cases n with
    | zero => exact ComposableArrows.exact₁ R
    | succ n =>
      have hd : d ≫ E.sequence.map' 2 3 = 0 := by
        apply pushout.hom_ext
        · simp [d, ← Category.assoc]
        · simp [d, ← Category.assoc, g, E.exact.toIsComplex.zero 1]
      apply ComposableArrows.exact_of_δ₀
      · apply ComposableArrows.exact₂_mk _ hd
        apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
        intro B x hx
        obtain ⟨B', π, hπ, y, hy⟩ := (E.exact.exact 1).exact_up_to_refinements x hx
        refine ⟨B', π, hπ, y ≫ pushout.inr u j, ?_⟩
        change π ≫ x = (y ≫ pushout.inr u j) ≫ d
        simpa only [Category.assoc, d, pushout.inr_desc] using hy
      · exact E.exact.δ₀.δ₀
  have hT : T.Exact := by
    apply ComposableArrows.exact_of_δ₀
    · exact ComposableArrows.exact₂_mk _ (by change pushout.inl u j ≫ d = 0; simp [d])
        (pushout_exact_pair j g hz he u)
    · exact hR
  let c : E.sequence ⟶ T :=
    ComposableArrows.homMkSucc (E.leftIso.hom ≫ u)
      (ComposableArrows.homMkSucc (pushout.inr u j) (𝟙 E.sequence.δ₀.δ₀)
        (by
          change g ≫ 𝟙 _ = pushout.inr u j ≫ d
          simp [d])) (by
          change E.sequence.map' 0 1 ≫ pushout.inr u j =
            (E.leftIso.hom ≫ u) ≫ pushout.inl u j
          rw [Category.assoc, pushout.condition, ← Category.assoc]
          simp [j])
  have hc (k : Fin (n + 3)) (hk : 1 < k.val) : IsIso (c.app k) := by
    obtain ⟨k, hk'⟩ := k
    dsimp only [Fin.val] at hk
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k =>
        change IsIso (𝟙 _)
        infer_instance
  have hep : Epi (T.map' (n + 1) (n + 2)) := by
    have := E.last_epi
    have h := ComposableArrows.naturality' c (n + 1) (n + 2)
    have hi := hc ⟨n + 2, by omega⟩ (by dsimp; omega)
    have : Epi (E.sequence.map' (n + 1) (n + 2) ≫ c.app ⟨n + 2, by omega⟩) :=
      inferInstance
    exact epi_of_epi_fac h.symm
  let G : YonedaExtension A W U (n + 1) :=
    { sequence := T
      leftIso := Iso.refl W
      rightIso := E.rightIso
      exact := hT
      first_mono := by
        change Mono (pushout.inl u j)
        infer_instance
      last_epi := hep }
  refine ⟨G, c, ?_, ?_, ?_, hc⟩
  · change E.leftIso.inv ≫ (E.leftIso.hom ≫ u) ≫ 𝟙 W = u
    simp
  · change E.rightIso.inv ≫ (𝟙 _) ≫ E.rightIso.hom = 𝟙 U
    simp
  · change IsPushout j u (pushout.inr u j) ((𝟙 W) ≫ pushout.inl u j)
    simpa only [Category.id_comp] using (IsPushout.of_hasPushout u j).flip

set_option backward.isDefEq.respectTransparency false in
private theorem product_extension {V U : A} (n : ℕ)
    (E F : YonedaExtension A V U (n + 1)) :
    ∃ (T : YonedaExtension A (Limits.prod V V) (Limits.prod U U) (n + 1))
      (p₁ : T.sequence ⟶ E.sequence) (p₂ : T.sequence ⟶ F.sequence),
      T.leftMap E p₁ = prod.fst ∧ T.leftMap F p₂ = prod.snd ∧
      T.rightMap E p₁ = prod.fst ∧ T.rightMap F p₂ = prod.snd ∧
      ∀ k : Fin (n + 3), Nonempty (IsLimit (BinaryFan.mk (p₁.app k) (p₂.app k))) := by
  let S : ComposableArrows A (n + 2) :=
    { obj := fun i => Limits.prod (E.sequence.obj i) (F.sequence.obj i)
      map := fun f => prod.map (E.sequence.map f) (F.sequence.map f)
      map_id := by intro i; simp
      map_comp := by intro i j k f g; simp [prod.map_map] }
  have hz (i : ℕ) (hi : i + 2 ≤ n + 2) : S.map' i (i + 1) ≫
      S.map' (i + 1) (i + 2) = 0 := by
    apply prod.hom_ext <;>
      simp [S, E.exact.toIsComplex.zero i,
        F.exact.toIsComplex.zero i]
  have he : S.Exact := by
    refine ⟨⟨hz⟩, fun i hi => ?_⟩
    apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
    intro B x hx
    have hx₁ : (x ≫ prod.fst) ≫ E.sequence.map' (i + 1) (i + 2) = 0 := by
      have h := congrArg (fun f => f ≫ prod.fst) hx
      simpa [S, Category.assoc] using h
    obtain ⟨B₁, π₁, hπ₁, y₁, hy₁⟩ :=
      (E.exact.exact i).exact_up_to_refinements (x ≫ prod.fst) hx₁
    have hx₂ : (π₁ ≫ x ≫ prod.snd) ≫ F.sequence.map' (i + 1) (i + 2) = 0 := by
      have h := congrArg (fun f => π₁ ≫ f ≫ prod.snd) hx
      simpa [S, Category.assoc] using h
    obtain ⟨B₂, π₂, hπ₂, y₂, hy₂⟩ :=
      (F.exact.exact i).exact_up_to_refinements (π₁ ≫ x ≫ prod.snd) hx₂
    refine ⟨B₂, π₂ ≫ π₁, inferInstance, prod.lift (π₂ ≫ y₁) y₂, ?_⟩
    apply prod.hom_ext
    · simpa [S, Category.assoc] using congrArg (fun f => π₂ ≫ f) hy₁
    · simpa [S, Category.assoc] using hy₂
  let T : YonedaExtension A (Limits.prod V V) (Limits.prod U U) (n + 1) :=
    { sequence := S
      leftIso := prod.mapIso E.leftIso F.leftIso
      rightIso := prod.mapIso E.rightIso F.rightIso
      exact := he
      first_mono := by
        have := E.first_mono
        have := F.first_mono
        change Mono (prod.map _ _)
        infer_instance
      last_epi := by
        have := E.last_epi
        have := F.last_epi
        change Epi (prod.map _ _)
        infer_instance }
  let p₁ : T.sequence ⟶ E.sequence :=
    { app := fun _ => prod.fst
      naturality := by intros; simp [T, S] }
  let p₂ : T.sequence ⟶ F.sequence :=
    { app := fun _ => prod.snd
      naturality := by intros; simp [T, S] }
  refine ⟨T, p₁, p₂, ?_, ?_, ?_, ?_, fun k => ⟨prodIsProd _ _⟩⟩
  · simp [leftMap, T, p₁, prod.mapIso]
  · simp [leftMap, T, p₂, prod.mapIso]
  · rw [rightMap]
    change prod.map E.rightIso.inv F.rightIso.inv ≫ prod.fst ≫ E.rightIso.hom = _
    rw [← Category.assoc, prod.map_fst, Category.assoc, E.rightIso.inv_hom_id, Category.comp_id]
  · rw [rightMap]
    change prod.map E.rightIso.inv F.rightIso.inv ≫ prod.snd ≫ F.rightIso.hom = _
    rw [← Category.assoc, prod.map_snd, Category.assoc, F.rightIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Pull back the final epimorphism of a finite extension along an endpoint map.
Source: Stacks Project, Homology Section 010I, pullback of extensions.
Proof: use the actual pullback in degree one. In higher degrees pull back the
canonical cokernel tail inductively and reattach the first two terms. Exactness
is preserved by the epic cokernel projection and the monic first tail arrow.
(blueprint: lem-coef-yoneda-baer-existence) -/
theorem pullback_extension {V U W : A} (n : ℕ)
    (E : YonedaExtension A V U (n + 1)) (u : W ⟶ U) :
    ∃ (P : YonedaExtension A V W (n + 1)) (b : P.sequence ⟶ E.sequence),
      P.leftMap E b = 𝟙 V ∧ P.rightMap E b = u ∧
      IsPullback (b.app ⟨n + 1, by omega⟩)
        (P.sequence.map' (n + 1) (n + 2) ≫ P.rightIso.hom)
        (E.sequence.map' (n + 1) (n + 2) ≫ E.rightIso.hom) u ∧
      ∀ k : Fin (n + 3), k.val < n + 1 → IsIso (b.app k) := by
  induction n generalizing V U W with
  | zero =>
    let j := E.leftIso.inv ≫ E.sequence.map' 0 1
    let g := E.sequence.map' 1 2 ≫ E.rightIso.hom
    have hz : j ≫ g = 0 := by
      simp only [j, g, Category.assoc]
      rw [← Category.assoc (E.sequence.map' 0 1), E.exact.toIsComplex.zero 0]
      simp
    let d : V ⟶ pullback g u := pullback.lift j 0 (by simp [hz])
    have hd : d ≫ pullback.snd g u = 0 := by simp [d]
    let S := ShortComplex.mk j g hz
    let φ : S ⟶ E.sequence.sc E.exact.toIsComplex 0 :=
      { τ₁ := E.leftIso.inv
        τ₂ := 𝟙 _
        τ₃ := E.rightIso.inv
        comm₁₂ := by simp [S, j]
        comm₂₃ := by simp [S, g] }
    have he : S.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (E.exact.exact 0)
    have hex : (ShortComplex.mk d (pullback.snd g u) hd).Exact := by
      apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
      intro B x hx
      have hx' : (x ≫ pullback.fst g u) ≫ g = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx, zero_comp]
      obtain ⟨B', π, hπ, y, hy⟩ := he.exact_up_to_refinements _ hx'
      refine ⟨B', π, hπ, y, ?_⟩
      apply pullback.hom_ext
      · simpa [d, Category.assoc] using hy
      · simp [d, Category.assoc, hx]
    have hj : Mono j := by have := E.first_mono; dsimp [j]; infer_instance
    have hm : Mono d := mono_of_mono_fac (by simp [d] : d ≫ pullback.fst g u = j)
    have hg : Epi g := by have := E.last_epi; dsimp [g]; infer_instance
    let P : YonedaExtension A V W 1 :=
      { sequence := ComposableArrows.mk₂ d (pullback.snd g u)
        leftIso := Iso.refl _
        rightIso := Iso.refl _
        exact := ComposableArrows.exact₂_mk _ hd hex
        first_mono := hm
        last_epi := by change Epi (pullback.snd g u); infer_instance }
    let b : P.sequence ⟶ E.sequence :=
      ComposableArrows.homMk₂ E.leftIso.inv (pullback.fst g u)
        (u ≫ E.rightIso.inv) (by simp [P, d, j]) (by
          change pullback.snd g u ≫ (u ≫ E.rightIso.inv) =
            pullback.fst g u ≫ E.sequence.map' 1 2
          rw [← Category.assoc, ← pullback.condition]
          simp [g])
    refine ⟨P, b, ?_, ?_, ?_, ?_⟩
    · change (𝟙 V) ≫ E.leftIso.inv ≫ E.leftIso.hom = 𝟙 V
      simp
    · change (𝟙 W) ≫ (u ≫ E.rightIso.inv) ≫ E.rightIso.hom = u
      simp
    · change IsPullback (pullback.fst g u) (pullback.snd g u ≫ 𝟙 W) g u
      simpa only [Category.comp_id] using (IsPullback.of_hasPullback g u)
    · intro k hk
      have h : k = 0 := Fin.ext (by simpa using (show k.val = 0 by omega))
      subst k
      change IsIso E.leftIso.inv
      infer_instance
  | succ n ih =>
    obtain ⟨P, b, hl, hr, hp, hi⟩ := ih E.tail u
    let a := E.sequence.map' 0 1
    let q := cokernel.π a ≫ P.leftIso.inv
    let d := q ≫ P.sequence.map' 0 1
    have hq : Epi q := by dsimp [q]; infer_instance
    have hd : a ≫ d = 0 := by simp [d, q, ← Category.assoc, a]
    let T := (P.sequence.δ₀.precomp d).precomp a
    have hR : (P.sequence.δ₀.precomp d).Exact := by
      apply ComposableArrows.exact_of_δ₀
      · have hz : d ≫ P.sequence.map' 1 2 = 0 := by
          simp [d, Category.assoc, P.exact.toIsComplex.zero 0]
        apply ComposableArrows.exact₂_mk _ hz
        let φ : ShortComplex.mk d (P.sequence.map' 1 2) hz ⟶
            P.sequence.sc P.exact.toIsComplex 0 :=
          { τ₁ := q
            τ₂ := 𝟙 _
            τ₃ := 𝟙 _
            comm₁₂ := by simp [d]
            comm₂₃ := by simp }
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (P.exact.exact 0)
      · exact P.exact.δ₀
    have hT : T.Exact := by
      apply ComposableArrows.exact_of_δ₀
      · apply ComposableArrows.exact₂_mk _ hd
        have := P.first_mono
        let φ : E.head ⟶ ShortComplex.mk a d hd :=
          { τ₁ := 𝟙 _
            τ₂ := 𝟙 _
            τ₃ := P.leftIso.inv ≫ P.sequence.map' 0 1
            comm₁₂ := by simp [head, a]
            comm₂₃ := by simp [d, q, head, a, Category.assoc] }
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 E.head_shortExact.exact
      · exact hR
    have hb₀ : P.leftIso.inv ≫ b.app 0 = 𝟙 _ := by
      change P.leftIso.inv ≫ b.app 0 ≫ 𝟙 _ = 𝟙 _ at hl
      simpa only [Category.comp_id] using hl
    have hw : d ≫ b.app ⟨1, by omega⟩ = E.sequence.map' 1 2 := by
      dsimp only [d, q]
      rw [Category.assoc, Category.assoc, ComposableArrows.naturality' b 0 1,
        ← Category.assoc P.leftIso.inv]
      erw [hb₀, Category.id_comp]
      change cokernel.π a ≫ cokernel.desc a _ _ = _
      simp
    let b' := ComposableArrows.δ₀Functor.map b
    let c : T ⟶ E.sequence :=
      ComposableArrows.homMkSucc (𝟙 _)
        (ComposableArrows.homMkSucc (𝟙 _) b'
          (by
            change d ≫ b.app ⟨1, by omega⟩ = 𝟙 _ ≫ E.sequence.map' 1 2
            simpa only [Category.id_comp] using hw))
        (by change a ≫ 𝟙 _ = 𝟙 _ ≫ a; simp)
    let G : YonedaExtension A V W (n + 2) :=
      { sequence := T
        leftIso := E.leftIso
        rightIso := P.rightIso
        exact := hT
        first_mono := E.first_mono
        last_epi := P.last_epi }
    refine ⟨G, c, ?_, ?_, ?_, ?_⟩
    · change E.leftIso.inv ≫ 𝟙 _ ≫ E.leftIso.hom = 𝟙 V
      simp
    · change P.rightIso.inv ≫ b.app (Fin.last (n + 2)) ≫ E.rightIso.hom = u
      exact hr
    · change IsPullback (b.app ⟨n + 1, by omega⟩)
        (P.sequence.map' (n + 1) (n + 2) ≫ P.rightIso.hom)
        (E.sequence.map' (n + 2) (n + 3) ≫ E.rightIso.hom) u
      exact hp
    · intro k hk
      obtain ⟨k, hk'⟩ := k
      cases k with
      | zero => change IsIso (𝟙 _); infer_instance
      | succ k =>
        cases k with
        | zero => change IsIso (𝟙 _); infer_instance
        | succ k =>
          change IsIso (b.app ⟨k + 1, by omega⟩)
          exact hi ⟨k + 1, by omega⟩ (by dsimp at hk ⊢; omega)

/-- The termwise product, diagonal pullback, and addition pushout construction
exists as an exact extension with all the specified comparison maps.
Source: Stacks Project, Homology Section 010I, Baer sum construction.
Proof: form the termwise binary product of E and F. Finite products are biproducts
in an abelian category, so the sequence is exact and its endpoint arrows remain
monic and epic. Pull back the last epimorphism along the diagonal of U, changing
only the last middle object and the right endpoint. The earlier arrow factors
through the pullback because its composite to the product endpoint is zero.
Pullback stability of epimorphisms and the kernel universal property give
exactness. Push out the first monomorphism along addition on V. The following
arrow descends because it kills that monomorphism. Pushout stability of
monomorphisms and the cokernel universal property give exactness. All unchanged
middle terms have identity comparison maps. For degree one perform the same
two operations successively on the single middle object; the short exact
pullback and pushout lemmas give both exactness assertions. The product
projections, pullback map, and pushout map satisfy exactly BaerSum's equations.
(blueprint: lem-coef-yoneda-baer-existence) -/
theorem baerSum_exists (V U : A) (n : ℕ) (E F : YonedaExtension A V U (n + 1)) :
    ∃ G : YonedaExtension A V U (n + 1), BaerSum E F G := by
  obtain ⟨T, p₁, p₂, hl₁, hl₂, hr₁, hr₂, ht⟩ := product_extension n E F
  obtain ⟨P, b, hbl, hbr, hpb, hb⟩ :=
    pullback_extension n T (prod.lift (𝟙 U) (𝟙 U))
  obtain ⟨G, c, hcl, hcr, hpo, hc⟩ :=
    pushout_extension n P (prod.fst + prod.snd)
  exact ⟨G, T, P, p₁, p₂, b, c, hl₁, hl₂, hr₁, hr₂, ht,
    hbl, hbr, hpb, hb, hcl, hcr, hpo, hc⟩

end CategoryTheory.YonedaExtension
