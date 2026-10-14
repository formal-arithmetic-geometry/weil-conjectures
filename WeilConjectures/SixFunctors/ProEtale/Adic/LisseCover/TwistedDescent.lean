/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Constant
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine descent of finite twisted sheaves

Let `f : V ⟶ Y` be weakly étale, `c` a descent cocycle on the constant sheaf with finite fibre
`Fin N`, and `s : S ⟶ Y` an open immersion from an affine scheme, covered by an affine
`p : W ⟶ S` (flat and surjective) mapping to `V` through `j : W ⟶ V`. The trivial cover
`∐_{Fin N} W ⟶ W` carries the coaction transporting the summands along `c`, and affine flat
descent (`AlgebraicGeometry.exists_isPullback_of_coaction`) descends it to a finite étale
`n : N ⟶ S`. Its `S`-morphisms from étale `Y`-schemes over `S` are the sections of the sheaf
of sets defined by `c`
(`AlgebraicGeometry.TwistedDescent.isUniversalSection`, in the sense of
`AlgebraicGeometry.Scheme.IsUniversalSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.TwistedDescent

open Scheme

section Index

variable (N : ℕ) (W : Scheme.{u})

/-- The trivial cover `∐_{Fin N} W` of `W`. -/
noncomputable abbrev triv : Scheme.{u} := ∐ fun _ : ULift.{u} (Fin N) ↦ W

/-- The projection `∐_{Fin N} W ⟶ W`. -/
noncomputable abbrev trivπ : triv N W ⟶ W := Sigma.desc fun _ ↦ 𝟙 W

/-- The index of a point of `∐_{Fin N} W`. -/
noncomputable def idx (x : ↥(triv N W)) : Fin N := (sigmaIdx (ULift.{u} (Fin N)) W x).down

variable {N W}

/-- The morphism into the trivial cover given by a locally constant index function. -/
noncomputable def ofIdx {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) : T ⟶ triv N W :=
  (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w φ).1

lemma ofIdx_trivπ {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) :
    ofIdx w φ ≫ trivπ N W = w :=
  (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w φ).2

lemma idx_ofIdx {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) (z : T) :
    idx N W ((ofIdx w φ).base z) = φ z := by
  have := congrArg (fun ψ : C(T, Fin N) ↦ ψ z)
    ((sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w).left_inv φ)
  exact this

/-- Morphisms into the trivial cover are determined by their projection and their index. -/
lemma hom_ext_triv {T : Scheme.{u}} {a b : T ⟶ triv N W} (h : a ≫ trivπ N W = b ≫ trivπ N W)
    (hidx : ∀ z, idx N W (a.base z) = idx N W (b.base z)) : a = b := by
  have := (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm
    (b ≫ trivπ N W)).symm.injective (a₁ := ⟨a, h⟩) (a₂ := ⟨b, rfl⟩)
    (ContinuousMap.ext fun z ↦ hidx z)
  exact congrArg Subtype.val this

lemma continuous_idx : Continuous (idx N W) :=
  continuous_uliftDown.comp (sigmaIdx (ULift.{u} (Fin N)) W).continuous

end Index

/-- The inverse of a self-map of a finite set, as a function of the self-map. -/
noncomputable def finInv {N : ℕ} (g : Fin N → Fin N) (a : Fin N) : Fin N :=
  if h : ∃ b, g b = a then h.choose else a

lemma finInv_apply {N : ℕ} {g : Fin N → Fin N} (hg : Function.Injective g) (b : Fin N) :
    finInv g (g b) = b := by
  have h : ∃ b', g b' = g b := ⟨b, rfl⟩
  simp only [finInv, dif_pos h]
  exact hg h.choose_spec

lemma apply_finInv {N : ℕ} {g : Fin N → Fin N} (hg : Function.Surjective g) (a : Fin N) :
    g (finInv g a) = a := by
  have h : ∃ b, g b = a := hg a
  simp only [finInv, dif_pos h]
  exact h.choose_spec

lemma finInv_id {N : ℕ} (a : Fin N) : finInv id a = a :=
  finInv_apply (g := id) Function.injective_id a

/-- A descent cocycle on a finite set is locally constant as a function to self-maps. -/
lemma _root_.AlgebraicGeometry.IsDescentCocycle.isLocallyConstant_fun {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ}
    {c : ↥(pullback f f) → Fin N → Fin N} (hc : IsDescentCocycle f c) :
    IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  have : ∀ᶠ z in nhds z₀, ∀ a, c z a = c z₀ a :=
    Filter.eventually_all.2 fun a ↦ (IsLocallyConstant.iff_eventually_eq _).1
      (hc.isLocallyConstant a) z₀
  filter_upwards [this] with z hz
  exact funext hz

section Coaction

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ} {c : ↥(pullback f f) → Fin N → Fin N}
  (hc : IsDescentCocycle f c) {S W : Scheme.{u}} {s : S ⟶ Y} {j : W ⟶ V} {p : W ⟶ S}
  (hjp : j ≫ f = p ≫ s)

include hjp in
lemma kappa_w : (pullback.fst (trivπ N W ≫ p) p ≫ trivπ N W) ≫ j ≫ f =
    pullback.snd (trivπ N W ≫ p) p ≫ j ≫ f := by
  rw [hjp, Category.assoc, ← Category.assoc (trivπ N W), pullback.condition_assoc]

/-- The map `(∐_{Fin N} W) ×_S W ⟶ W ×_Y W` to the pairs of points of `W`. -/
noncomputable def kappa : pullback (trivπ N W ≫ p) p ⟶ pullback (j ≫ f) (j ≫ f) :=
  pullback.lift _ _ (kappa_w hjp)

include hc in
lemma continuous_coactIdx : Continuous fun x : ↥(pullback (trivπ N W ≫ p) p) ↦
    finInv (c ((pairRestrict j).base ((kappa hjp).base x)))
      (idx N W ((pullback.fst (trivπ N W ≫ p) p).base x)) := by
  refine IsLocallyConstant.continuous ?_
  exact IsLocallyConstant.comp₂ (f := fun x ↦ c ((pairRestrict j).base ((kappa hjp).base x)))
    (g := fun x ↦ idx N W ((pullback.fst (trivπ N W ≫ p) p).base x))
    ((hc.isLocallyConstant_fun.comp_continuous (pairRestrict j).base.hom.continuous).comp_continuous
      (kappa hjp).base.hom.continuous)
    ((IsLocallyConstant.iff_continuous _).2
      (continuous_idx.comp (pullback.fst (trivπ N W ≫ p) p).base.hom.continuous)) finInv

/-- The coaction `(∐_{Fin N} W) ×_S W ⟶ ∐_{Fin N} W`, transporting the summands along `c`. -/
noncomputable def coact : pullback (trivπ N W ≫ p) p ⟶ triv N W :=
  ofIdx (pullback.snd _ _) ⟨_, continuous_coactIdx hc hjp⟩

lemma coact_trivπ : coact hc hjp ≫ trivπ N W = pullback.snd (trivπ N W ≫ p) p :=
  ofIdx_trivπ _ _

lemma idx_coact (x : ↥(pullback (trivπ N W ≫ p) p)) :
    idx N W ((coact hc hjp).base x) = finInv (c ((pairRestrict j).base ((kappa hjp).base x)))
      (idx N W ((pullback.fst (trivπ N W ≫ p) p).base x)) :=
  idx_ofIdx _ _ x

@[reassoc]
lemma kappa_fst : kappa hjp ≫ pullback.fst (j ≫ f) (j ≫ f) =
    pullback.fst (trivπ N W ≫ p) p ≫ trivπ N W := pullback.lift_fst _ _ _

@[reassoc]
lemma kappa_snd : kappa hjp ≫ pullback.snd (j ≫ f) (j ≫ f) = pullback.snd (trivπ N W ≫ p) p :=
  pullback.lift_snd _ _ _

include hc in
lemma coact_counit : coactionUnit p (trivπ N W) ≫ coact hc hjp = 𝟙 (triv N W) := by
  refine hom_ext_triv ?_ fun x ↦ ?_
  · rw [Category.assoc, coact_trivπ, pullback.lift_snd, Category.id_comp]
  · have hk : coactionUnit p (trivπ N W) ≫ kappa hjp ≫ pairRestrict j =
        trivπ N W ≫ j ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [kappa_fst_assoc]; rfl
      · simp [kappa_snd_assoc]
    rw [Scheme.Hom.comp_apply, idx_coact]
    have e₁ : (pairRestrict j).base ((kappa hjp).base ((coactionUnit p (trivπ N W)).base x)) =
        (pullback.diagonal f).base (j.base ((trivπ N W).base x)) := by
      simp only [← Scheme.Hom.comp_apply, Category.assoc, hk]
    have e₂ : (pullback.fst (trivπ N W ≫ p) p).base ((coactionUnit p (trivπ N W)).base x) = x := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
      rfl
    rw [e₁, e₂, hc.diagonal, finInv_id]
    rfl

include hc in
lemma coact_coassoc : coactionMap p (trivπ N W) (coact hc hjp) (coact_trivπ hc hjp) ≫
    coact hc hjp = coactionForget p (trivπ N W) ≫ coact hc hjp := by
  set Z := pullback (pullback.snd (trivπ N W ≫ p) p ≫ p) p
  set cM := coactionMap p (trivπ N W) (coact hc hjp) (coact_trivπ hc hjp)
  set cF := coactionForget p (trivπ N W)
  set z₁ := pullback.fst (pullback.snd (trivπ N W ≫ p) p ≫ p) p
  have hcM₁ : cM ≫ pullback.fst _ _ = z₁ ≫ coact hc hjp := by simp [cM, z₁]
  have hcM₂ : cM ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [cM]
  have hcF₁ : cF ≫ pullback.fst _ _ = z₁ ≫ pullback.fst _ _ := by simp [cF, z₁]
  have hcF₂ : cF ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [cF]
  refine hom_ext_triv ?_ fun x ↦ ?_
  · rw [Category.assoc, Category.assoc, coact_trivπ, hcM₂, hcF₂]
  · -- the triple of points `(w₁, w₂, w₃)`
    have hΘ : (z₁ ≫ kappa hjp) ≫ pullback.snd (j ≫ f) (j ≫ f) =
        (cM ≫ kappa hjp) ≫ pullback.fst (j ≫ f) (j ≫ f) := by
      rw [Category.assoc, kappa_snd, Category.assoc, kappa_fst, reassoc_of% hcM₁, coact_trivπ]
    let Θ : Z ⟶ tripleProduct (j ≫ f) := pullback.lift _ _ hΘ
    have hΘ₁₃ : Θ ≫ tripleProj₁₃ (j ≫ f) = cF ≫ kappa hjp := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
          kappa_fst, Category.assoc, kappa_fst, reassoc_of% hcF₁]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
          kappa_snd, Category.assoc, kappa_snd, hcM₂, hcF₂]
    have hco := hc.restrict.cocycle (Θ.base x)
    have e₁ : Θ ≫ pullback.fst _ _ = z₁ ≫ kappa hjp := pullback.lift_fst _ _ _
    have e₂ : Θ ≫ pullback.snd _ _ = cM ≫ kappa hjp := pullback.lift_snd _ _ _
    simp only [← Scheme.Hom.comp_apply, hΘ₁₃, e₁, e₂, restrictCocycle] at hco
    simp only [Scheme.Hom.comp_apply] at hco
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, idx_coact, idx_coact]
    have q₁ : (pullback.fst (trivπ N W ≫ p) p).base (cM.base x) = (coact hc hjp).base (z₁.base x) := by
      rw [← Scheme.Hom.comp_apply, hcM₁, Scheme.Hom.comp_apply]
    have q₂ : (pullback.fst (trivπ N W ≫ p) p).base (cF.base x) =
        (pullback.fst (trivπ N W ≫ p) p).base (z₁.base x) := by
      rw [← Scheme.Hom.comp_apply, hcF₁, Scheme.Hom.comp_apply]
    rw [q₁, idx_coact, q₂, hco]
    set A := c ((pairRestrict j).base ((kappa hjp).base (cM.base x)))
    set B := c ((pairRestrict j).base ((kappa hjp).base (z₁.base x)))
    set i := idx N W ((pullback.fst (trivπ N W ≫ p) p).base (z₁.base x))
    have hA := hc.bijective ((pairRestrict j).base ((kappa hjp).base (cM.base x)))
    have hB := hc.bijective ((pairRestrict j).base ((kappa hjp).base (z₁.base x)))
    have hBA : Function.Injective (B ∘ A) := hB.1.comp hA.1
    rw [← finInv_apply hBA (finInv A (finInv B i))]
    rw [Function.comp_apply, apply_finInv (g := A) hA.2, apply_finInv (g := B) hB.2]

end Coaction

end AlgebraicGeometry.TwistedDescent
