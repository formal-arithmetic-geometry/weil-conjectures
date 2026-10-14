/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descending a representing finite étale scheme along an affine étale cover

Let `E` be a sheaf of sets on the small étale site of an affine scheme `T`, and let
`p : X ⟶ T` be a surjective étale morphism from an affine scheme. Suppose that the restriction
of `E` to étale `X`-schemes is represented by a finite étale `X`-scheme `v : V ⟶ X`, with
universal section `ξ ∈ E(V)` (`AlgebraicGeometry.Scheme.IsUniversalSection`). Then `E` itself is
represented by a finite étale `T`-scheme (`AlgebraicGeometry.Scheme.IsUniversalSection.descend`).

This is the descent step in the proof that finite locally constant sheaves are represented by
finite étale schemes (blueprint `lemma-weil-pbc-finite-locally-constant-etale-equivalence`): the
two pullbacks of `ξ` to `V ×_T X` give, by universality, the descent isomorphism
`γ : V ×_T X ⟶ V` (the transport of the first projection to the second), which satisfies the
counit and cocycle identities because both sides pull `ξ` back to the same section. Affine flat
descent in coaction form (`AlgebraicGeometry.exists_isPullback_of_coaction`, Stacks 023N)
produces `N` over `T` with `V ≅ N ×_T X`; `N` is finite étale by fpqc descent of these
properties, `ξ` descends to `ξ₀ ∈ E(N)` by the sheaf property along `V ⟶ N`, and `ξ₀` is
universal, by descending morphisms along the effective epimorphism `W ×_T X ⟶ W`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {E : T.Etaleᵒᵖ ⥤ Type w} {X : Scheme.{u}} {p : X ⟶ T}
  [AlgebraicGeometry.Etale p] {V : Scheme.{u}} {v : V ⟶ X} [AlgebraicGeometry.Etale v]
  {ξ : E.obj (op (Etale.mk (v ≫ p)))}

namespace IsUniversalSection

variable (p v) in
/-- The fibre product `V ×_T X`, an étale `T`-scheme through the second projection. -/
noncomputable abbrev coactObj : T.Etale := Etale.mk (pullback.snd (v ≫ p) p ≫ p)

variable (p v) in
/-- The first projection `V ×_T X ⟶ V`, a morphism of étale `T`-schemes. -/
noncomputable abbrev coactFst : coactObj p v ⟶ Etale.mk (v ≫ p) :=
  Over.homMk (pullback.fst (v ≫ p) p) pullback.condition

/-- A `T`-morphism `W ⟶ V` together with a `T`-morphism `W ⟶ X` gives a `T`-morphism
`W ⟶ V ×_T X`. -/
noncomputable abbrev coactLift {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p)) (x : W.left ⟶ X)
    (hx : x ≫ p = W.hom) : W ⟶ coactObj p v :=
  Over.homMk (pullback.lift a.left x (by exact (Over.w a).trans hx.symm)) (by
    change pullback.lift _ _ _ ≫ pullback.snd (v ≫ p) p ≫ p = _
    rw [pullback.lift_snd_assoc, hx])

lemma coactLift_fst {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p)) (x : W.left ⟶ X)
    (hx : x ≫ p = W.hom) : coactLift a x hx ≫ coactFst p v = a :=
  Over.Hom.ext (by
    change pullback.lift a.left x _ ≫ pullback.fst (v ≫ p) p = a.left
    exact pullback.lift_fst _ _ _)

lemma coactLift_left_snd {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p)) (x : W.left ⟶ X)
    (hx : x ≫ p = W.hom) : (coactLift a x hx).left ≫ pullback.snd (v ≫ p) p = x := by
  change pullback.lift a.left x _ ≫ pullback.snd (v ≫ p) p = x
  exact pullback.lift_snd _ _ _

variable (h : IsUniversalSection E p (Etale.mk (v ≫ p)) v ξ)

/-- The descent isomorphism of a universal section: the morphism `γ : V ×_T X ⟶ V` over the
second projection which pulls `ξ` back to the pullback of `ξ` along the first projection. -/
noncomputable def coact : coactObj p v ⟶ Etale.mk (v ≫ p) :=
  (h.exists_hom (W := coactObj p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst p v).op ξ)).choose

lemma coact_left_comp : (h.coact).left ≫ v = pullback.snd (v ≫ p) p :=
  (h.exists_hom (W := coactObj p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst p v).op ξ)).choose_spec.1

lemma map_coact : E.map h.coact.op ξ = E.map (coactFst p v).op ξ :=
  (h.exists_hom (W := coactObj p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst p v).op ξ)).choose_spec.2

/-- **The key identity**: for a `T`-morphism `a : W ⟶ V` and a `T`-morphism `x : W ⟶ X`, the
transport `(a, x) ≫ γ` of `a` to `x` is the unique `X`-morphism `b : W ⟶ V` over `x` with
`b^* ξ = a^* ξ`. -/
lemma coactLift_coact {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p)) (x : W.left ⟶ X)
    (hx : x ≫ p = W.hom) (b : W ⟶ Etale.mk (v ≫ p)) (hb : b.left ≫ v = x)
    (hab : E.map b.op ξ = E.map a.op ξ) : coactLift a x hx ≫ h.coact = b := by
  refine h.hom_ext ?_ ?_ ?_
  · rw [Etale.comp_left_eq, Category.assoc, coact_left_comp, hb, coactLift_left_snd]
  · rw [Etale.comp_left_eq, Category.assoc, Category.assoc, reassoc_of% (coact_left_comp h),
      reassoc_of% (coactLift_left_snd a x hx), hx]
  · rw [op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
      coactLift_fst, hab]

lemma coact_counit :
    coactionUnit p v ≫ (h.coact).left = 𝟙 V := by
  have := h.coactLift_coact (W := Etale.mk (v ≫ p)) (𝟙 _) v rfl (𝟙 _) (Category.id_comp _) rfl
  have e : coactionUnit p v = (coactLift (𝟙 (Etale.mk (v ≫ p))) v rfl).left :=
    pullback.hom_ext (by simp; rfl) (by simp)
  rw [e]
  exact congrArg (fun f ↦ f.left) this

lemma coact_coassoc :
    coactionMap p v (h.coact).left (h.coact_left_comp) ≫ (h.coact).left =
      coactionForget p v ≫ (h.coact).left := by
  -- the scheme `(V ×_T X) ×_T X`, as an étale `T`-scheme through the last projection
  let Z₂ : T.Etale := Etale.mk (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p ≫ p)
  let fst₂ : Z₂ ⟶ coactObj p v := Over.homMk (pullback.fst _ _) pullback.condition
  let Fe : Z₂ ⟶ coactObj p v := Over.homMk (coactionForget p v) (by
    change coactionForget p v ≫ pullback.snd (v ≫ p) p ≫ p = pullback.snd _ _ ≫ p
    simp)
  let m : Z₂ ⟶ Etale.mk (v ≫ p) := fst₂ ≫ h.coact
  have hm : E.map m.op ξ = E.map (fst₂ ≫ coactFst p v).op ξ := by
    rw [op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp]
  have h₁ := h.coactLift_coact (W := Z₂) m (pullback.snd _ _) rfl (Fe ≫ h.coact)
    (by
      change coactionForget p v ≫ h.coact.left ≫ v = _
      rw [coact_left_comp]
      simp)
    (by
      have hF : Fe ≫ coactFst p v = fst₂ ≫ coactFst p v := Over.Hom.ext (by
        change coactionForget p v ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _
        simp)
      rw [hm, op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
        hF])
  have e : coactionMap p v (h.coact).left h.coact_left_comp =
      (coactLift m (pullback.snd _ _) rfl).left := by
    apply pullback.hom_ext
    · change _ = pullback.lift (pullback.fst _ _ ≫ h.coact.left) _ _ ≫ pullback.fst _ _
      simp
    · change _ = pullback.lift (pullback.fst _ _ ≫ h.coact.left) _ _ ≫ pullback.snd _ _
      simp
  rw [e]
  exact congrArg (fun f ↦ f.left) h₁
include h in
/-- **Descent of a representing finite étale scheme along an affine étale cover.** Let `T` be
affine, `p : X ⟶ T` surjective étale with `X` affine, `E` a sheaf of sets on the small étale site
of `T`, and `ξ` a universal section of `E` relative to `p` along a finite étale `v : V ⟶ X`. Then
`E` is represented by a finite étale `T`-scheme `n : N ⟶ T`, with universal section `ξ₀`. The
pullback of `ξ₀` to `V = N ×_T X` is `ξ`.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem exists_isUniversalSection_of_isAffine [IsAffine X] [IsAffine T]
    [AlgebraicGeometry.Surjective p] [IsFinite v] (hE : Presheaf.IsSheaf T.smallEtaleTopology E) :
    ∃ (N : Scheme.{u}) (n : N ⟶ T) (_ : AlgebraicGeometry.Etale n) (_ : IsFinite n)
      (ξ₀ : E.obj (op (Etale.mk n))), IsUniversalSection E (𝟙 T) (Etale.mk n) n ξ₀ := by
  have : IsAffine V := isAffine_of_isAffineHom v
  obtain ⟨N, n, q, hq, hγq⟩ := exists_isPullback_of_coaction p v h.coact.left h.coact_left_comp
    h.coact_counit h.coact_coassoc
  have hpq : (@AlgebraicGeometry.Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hn : AlgebraicGeometry.Etale n :=
    of_isPullback_of_descendsAlong (P := @AlgebraicGeometry.Etale) hq.flip hpq
      (inferInstanceAs (AlgebraicGeometry.Etale v))
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hnf : IsFinite n :=
    of_isPullback_of_descendsAlong (P := @IsFinite) hq.flip hpq (inferInstanceAs (IsFinite v))
  have : AlgebraicGeometry.Surjective q := MorphismProperty.of_isPullback hq.flip ‹_›
  let NE : T.Etale := Etale.mk n
  let qE : Etale.mk (v ≫ p) ⟶ NE := Over.homMk q hq.w
  -- the section `ξ` descends along `q : V ⟶ N`
  obtain ⟨ξ₀, hξ₀⟩ := Etale.exists_map_eq_of_surjective hE qE q.surjective ξ (by
    intro Z p₁ p₂ hp
    have hp' : p₁.left ≫ q = p₂.left ≫ q := congrArg (fun f ↦ f.left) hp
    let ℓ := coactLift p₁ (p₂.left ≫ v) (Over.w p₂)
    have hℓ : ℓ ≫ h.coact = p₂ := by
      refine Over.Hom.ext (hq.hom_ext ?_ ?_)
      · change (ℓ.left ≫ h.coact.left) ≫ q = p₂.left ≫ q
        rw [Category.assoc, hγq, ← hp', ← Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · change (ℓ.left ≫ h.coact.left) ≫ v = p₂.left ≫ v
        rw [Category.assoc, coact_left_comp, coactLift_left_snd]
    rw [← hℓ, op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
      coactLift_fst])
  refine ⟨N, n, hn, hnf, ξ₀, IsUniversalSection.of_bijective fun W ↦ ?_⟩
  -- the base change `W' = W ×_T X ⟶ W`, a surjective étale cover
  let W' : T.Etale := Etale.mk (pullback.snd W.hom p ≫ p)
  let π : W' ⟶ W := Over.homMk (pullback.fst W.hom p) pullback.condition
  have hπ : Function.Surjective π.left := (pullback.fst W.hom p).surjective
  have : AlgebraicGeometry.Etale (pullback.fst W.hom p) := inferInstance
  have : LocallyOfFinitePresentation (pullback.fst W.hom p) := inferInstance
  have : Flat (pullback.fst W.hom p) := inferInstance
  have : EffectiveEpi π.left := inferInstanceAs (EffectiveEpi (pullback.fst W.hom p))
  -- the lift `W' ⟶ V` of a `T`-morphism `W ⟶ N`
  let lift (a : W ⟶ NE) : W' ⟶ Etale.mk (v ≫ p) :=
    Over.homMk (hq.lift (pullback.fst W.hom p ≫ a.left) (pullback.snd W.hom p) (by
      rw [Category.assoc, show a.left ≫ n = W.hom from Over.w a]
      exact pullback.condition)) (by
      change hq.lift _ _ _ ≫ v ≫ p = pullback.snd W.hom p ≫ p
      rw [hq.lift_snd_assoc])
  have lift_v (a : W ⟶ NE) : (lift a).left ≫ v = pullback.snd W.hom p := hq.lift_snd _ _ _
  have lift_q (a : W ⟶ NE) : lift a ≫ qE = π ≫ a := Over.Hom.ext (hq.lift_fst _ _ _)
  have map_lift (a : W ⟶ NE) : E.map (lift a).op ξ = E.map π.op (E.map a.op ξ₀) := by
    rw [← hξ₀, ← Functor.map_comp_apply, ← op_comp, lift_q, op_comp, Functor.map_comp_apply]
  refine ⟨fun a b hab ↦ ?_, fun e ↦ ?_⟩
  · have hab' : lift a = lift b := h.hom_ext ((lift_v a).trans (lift_v b).symm)
      (by rw [lift_v]; rfl) (by
        rw [map_lift, map_lift]
        exact congrArg _ hab)
    have : π ≫ a = π ≫ b := by rw [← lift_q, ← lift_q, hab']
    exact Over.Hom.ext ((cancel_epi (pullback.fst W.hom p)).1 (congrArg (fun f ↦ f.left) this))
  · obtain ⟨a', ha'v, ha'ξ⟩ := h.exists_hom (W := W') (pullback.snd W.hom p) rfl (E.map π.op e)
    -- the kernel pair of `π`, as an étale `T`-scheme
    let K : T.Etale := Etale.mk (pullback.fst π.left π.left ≫ W'.hom)
    let k₁ : K ⟶ W' := Over.homMk (pullback.fst π.left π.left) rfl
    let k₂ : K ⟶ W' := Over.homMk (pullback.snd π.left π.left) (by
      change pullback.snd π.left π.left ≫ W'.hom = pullback.fst π.left π.left ≫ W'.hom
      rw [← Over.w π, pullback.condition_assoc])
    have hk : k₁ ≫ π = k₂ ≫ π := Over.Hom.ext pullback.condition
    have hkq : pullback.fst π.left π.left ≫ a'.left ≫ q =
        pullback.snd π.left π.left ≫ a'.left ≫ q := by
      let ℓ := coactLift (k₁ ≫ a') (k₂.left ≫ pullback.snd W.hom p) (Over.w k₂)
      have hℓ : ℓ ≫ h.coact = k₂ ≫ a' := by
        refine h.coactLift_coact _ _ _ _ ?_ ?_
        · rw [Etale.comp_left_eq, Category.assoc, ha'v]
        · rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha'ξ,
            ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hk]
      have h1 : ℓ.left ≫ pullback.fst (v ≫ p) p = k₁.left ≫ a'.left :=
        congrArg (fun f : K ⟶ Etale.mk (v ≫ p) ↦ f.left) (coactLift_fst (k₁ ≫ a') _ _)
      have h2 := congrArg (fun f ↦ f.left ≫ q) hℓ
      change (ℓ.left ≫ h.coact.left) ≫ q = (k₂.left ≫ a'.left) ≫ q at h2
      rw [Category.assoc, hγq, ← Category.assoc, h1, Category.assoc, Category.assoc] at h2
      exact h2
    let aL : W.left ⟶ N := EffectiveEpi.desc π.left (a'.left ≫ q) (fun {Z} g₁ g₂ hg ↦ by
      calc g₁ ≫ a'.left ≫ q = pullback.lift g₁ g₂ hg ≫ pullback.fst π.left π.left ≫ a'.left ≫ q :=
            (pullback.lift_fst_assoc _ _ _ _).symm
        _ = pullback.lift g₁ g₂ hg ≫ pullback.snd π.left π.left ≫ a'.left ≫ q := by rw [hkq]
        _ = g₂ ≫ a'.left ≫ q := pullback.lift_snd_assoc _ _ _ _)
    have haL : π.left ≫ aL = a'.left ≫ q := EffectiveEpi.fac _ _ _
    let a : W ⟶ NE := Over.homMk aL (by
      change aL ≫ n = W.hom
      rw [← cancel_epi π.left, reassoc_of% haL, hq.w, reassoc_of% ha'v, Over.w π]
      rfl)
    refine ⟨a, Etale.map_injective_of_surjective hE π hπ ?_⟩
    have hπa : π ≫ a = a' ≫ qE := Over.Hom.ext haL
    rw [← Functor.map_comp_apply, ← op_comp, ← ha'ξ, ← hξ₀, ← Functor.map_comp_apply, ← op_comp,
      hπa]

end IsUniversalSection

end AlgebraicGeometry.Scheme
