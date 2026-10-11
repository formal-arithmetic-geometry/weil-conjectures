/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra

/-!
# Descent of affine schemes along a flat morphism of affine schemes

Let `p : W ⟶ S` be a flat morphism of affine schemes and `v : V ⟶ W` a morphism from an affine
scheme. A *coaction* on `V` relative to `W/S` is a morphism `γ : V ×_S W ⟶ V` over `W`
(i.e. `γ ≫ v = pr₂`) which is counital (`γ (x, v x) = x`) and coassociative
(`γ (γ (x, w₁), w₂) = γ (x, w₂)`); it is the descent datum of `V`, written as the transport of
a point `x` of `V` over `v x` to a point over `w`.

Every coaction is effective: there are an affine `S`-scheme `N` and a cartesian square
```
  V --q--> N
  |        |
  v        n
  v        v
  W --p--> S
```
with `q` invariant under the coaction, `γ ≫ q = pr₁ ≫ q`
(`AlgebraicGeometry.exists_isPullback_of_coaction`). On global sections the coaction is a descent
datum of algebras in the sense of `Algebra.DescentDatum`, and `N` is the spectrum of the
descended algebra (`Algebra.DescentDatum.descendedEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace AffineCoaction

variable {S W V : Scheme.{u}} (p : W ⟶ S) (v : V ⟶ W)

/-- `P = V ×_S W`. -/
noncomputable abbrev P : Scheme.{u} := pullback (v ≫ p) p

/-- `P₂ = V ×_S W ×_S W`. -/
noncomputable abbrev P₂ : Scheme.{u} := pullback (pullback.snd (v ≫ p) p ≫ p) p

/-- The diagonal `V ⟶ V ×_S W`, `x ↦ (x, v x)`. -/
noncomputable abbrev d : V ⟶ P p v := pullback.lift (𝟙 _) v (by simp)

/-- The projection `V ×_S W ×_S W ⟶ V ×_S W` forgetting the middle factor. -/
noncomputable abbrev π₁ : P₂ p v ⟶ P p v :=
  pullback.map _ _ _ _ (pullback.fst (v ≫ p) p) (𝟙 W) (𝟙 S) (by simp [pullback.condition])
    (by simp)

/-- The map `V ×_S W ×_S W ⟶ V ×_S W` applying `γ` to the first two factors. -/
noncomputable abbrev γ₁ (γ : P p v ⟶ V) (hγ : γ ≫ v = pullback.snd (v ≫ p) p) : P₂ p v ⟶ P p v :=
  pullback.map _ _ _ _ γ (𝟙 W) (𝟙 S) (by simp [reassoc_of% hγ]) (by simp)

end AffineCoaction

open AffineCoaction

variable {S W V : Scheme.{u}} [IsAffine S] [IsAffine W] [IsAffine V] (p : W ⟶ S) [Flat p]
  (v : V ⟶ W) (γ : P p v ⟶ V) (hγ : γ ≫ v = pullback.snd (v ≫ p) p)

/-- **Effectivity of affine descent along a flat morphism of affine schemes.** A counital and
coassociative coaction `γ : V ×_S W ⟶ V` over `W` on an affine `W`-scheme `V` descends: `V` is the
base change of an affine `S`-scheme `N` along `p`, through a morphism `q : V ⟶ N` which is
invariant under `γ`. -/
theorem exists_isPullback_of_coaction (hd : d p v ≫ γ = 𝟙 V)
    (hγγ : γ₁ p v γ hγ ≫ γ = π₁ p v ≫ γ) :
    ∃ (N : Scheme.{u}) (_ : IsAffine N) (n : N ⟶ S) (q : V ⟶ N),
      IsPullback q v n p ∧ γ ≫ q = pullback.fst (v ≫ p) p ≫ q := by
  -- the rings and their algebra structures
  let R : CommRingCat.{u} := Γ(S, ⊤)
  let A' : CommRingCat.{u} := Γ(W, ⊤)
  let E : CommRingCat.{u} := Γ(V, ⊤)
  let _ : Algebra R A' := p.appTop.hom.toAlgebra
  let _ : Algebra A' E := v.appTop.hom.toAlgebra
  let _ : Algebra R E := (v ≫ p).appTop.hom.toAlgebra
  have : IsScalarTower R A' E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have hflat : Module.Flat R A' := p.flat_appTop
  -- flat base change of global sections for `P = V ×_S W`
  have hP := isPushout_appTop_of_flat p (v ≫ p)
  let ξ : A' ⊗[R] E ≃+* Γ(P p v, ⊤) := hP.tensorEquiv rfl rfl
  have ξ_tmul : ∀ (a : A') (x : E),
      ξ (a ⊗ₜ x) = (pullback.snd (v ≫ p) p).appTop a * (pullback.fst (v ≫ p) p).appTop x :=
    hP.tensorEquiv_tmul rfl rfl
  -- the coaction on `E`
  let δ₀ : E →+* A' ⊗[R] E := ξ.symm.toRingHom.comp γ.appTop.hom
  have δ₀_apply : ∀ x, ξ (δ₀ x) = γ.appTop x := fun x ↦ by
    change ξ (ξ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hγv : ∀ a, γ.appTop (v.appTop a) = (pullback.snd (v ≫ p) p).appTop a := fun a ↦
    congr(((Scheme.Hom.appTop $hγ).hom) a)
  let δ : E →ₐ[A'] A' ⊗[R] E :=
    { δ₀ with
      commutes' := fun a ↦ by
        change δ₀ (algebraMap A' E a) = algebraMap A' (A' ⊗[R] E) a
        apply ξ.injective
        rw [δ₀_apply, Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        exact hγv a }
  have δ_apply : ∀ x, ξ (δ x) = γ.appTop x := δ₀_apply
  -- the counit condition
  have hd₁ : d p v ≫ pullback.fst (v ≫ p) p = 𝟙 _ := pullback.lift_fst _ _ _
  have hd₂ : d p v ≫ pullback.snd (v ≫ p) p = v := pullback.lift_snd _ _ _
  have hmul : ∀ t : A' ⊗[R] E,
      Algebra.TensorProduct.mulMap R A' E t = (d p v).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [ξ_tmul, map_mul, Algebra.TensorProduct.mulMap_tmul, Algebra.smul_def]
      have h1 : (d p v).appTop ((pullback.snd (v ≫ p) p).appTop a) = v.appTop a :=
        congr(((Scheme.Hom.appTop $hd₂).hom) a)
      have h2 : (d p v).appTop ((pullback.fst (v ≫ p) p).appTop x) = x :=
        congr(((Scheme.Hom.appTop $hd₁).hom) x)
      rw [h1, h2]
      rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcounit : ∀ x, Algebra.TensorProduct.mulMap R A' E (δ x) = x := fun x ↦ by
    rw [hmul, δ_apply]
    exact congr(((Scheme.Hom.appTop $hd).hom) x)
  -- the coassociativity condition, via `P₂ = P ×_S W`
  let _ : Algebra R Γ(P p v, ⊤) := (pullback.snd (v ≫ p) p ≫ p).appTop.hom.toAlgebra
  have hP₂ := isPushout_appTop_of_flat p (pullback.snd (v ≫ p) p ≫ p)
  let ξ₂ : A' ⊗[R] Γ(P p v, ⊤) ≃+* Γ(P₂ p v, ⊤) := hP₂.tensorEquiv rfl rfl
  have ξ₂_tmul : ∀ (a : A') (y : Γ(P p v, ⊤)), ξ₂ (a ⊗ₜ y) =
      (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p).appTop a *
        (pullback.fst (pullback.snd (v ≫ p) p ≫ p) p).appTop y :=
    hP₂.tensorEquiv_tmul rfl rfl
  let ξₐ : A' ⊗[R] E ≃ₐ[R] Γ(P p v, ⊤) :=
    { ξ with
      commutes' := fun r ↦ by
        change ξ (algebraMap R (A' ⊗[R] E) r) = algebraMap R Γ(P p v, ⊤) r
        rw [Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        rfl }
  have ξₐ_apply : ∀ t, ξₐ t = ξ t := fun _ ↦ rfl
  let Θ : A' ⊗[R] (A' ⊗[R] E) →+* Γ(P₂ p v, ⊤) :=
    ξ₂.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id R A') ξₐ.toAlgHom).toRingHom
  have Θ_inj : Function.Injective Θ := by
    have : ⇑Θ = ξ₂ ∘ (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ) := by
      ext t
      simp [Θ, Algebra.TensorProduct.congr_apply]
    rw [this]
    exact ξ₂.injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ).injective
  have Θ_tmul : ∀ (a : A') (t : A' ⊗[R] E), Θ (a ⊗ₜ t) =
      (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p).appTop a *
        (pullback.fst (pullback.snd (v ≫ p) p ≫ p) p).appTop (ξ t) := by
    intro a t
    simp [Θ, ξ₂_tmul, ξₐ_apply]
  have hγ₁₂ : γ₁ p v γ hγ ≫ pullback.snd (v ≫ p) p =
      pullback.snd (pullback.snd (v ≫ p) p ≫ p) p := by simp
  have hγ₁₁ : γ₁ p v γ hγ ≫ pullback.fst (v ≫ p) p = pullback.fst _ _ ≫ γ := by simp
  have hπ₁₂ : π₁ p v ≫ pullback.snd (v ≫ p) p =
      pullback.snd (pullback.snd (v ≫ p) p ≫ p) p := by simp
  have hπ₁₁ : π₁ p v ≫ pullback.fst (v ≫ p) p =
      pullback.fst _ _ ≫ pullback.fst (v ≫ p) p := by simp
  have hΘδ : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) t) =
      (γ₁ p v γ hγ).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, Θ_tmul,
        ξ_tmul, map_mul, δ_apply]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hγ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hγ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hΘinc : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A')
      (Algebra.TensorProduct.includeRight (R := R) (A := A') (B := E)) t) =
      (π₁ p v).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
        Θ_tmul, ξ_tmul, ξ_tmul, map_one, one_mul, map_mul]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hπ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hπ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcoassoc : ∀ x, Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) (δ x) =
      Algebra.TensorProduct.map (AlgHom.id R A') Algebra.TensorProduct.includeRight (δ x) := by
    intro x
    apply Θ_inj
    rw [hΘδ, hΘinc, δ_apply]
    exact congr(((Scheme.Hom.appTop $hγγ).hom) x)
  -- the descent datum and the descended algebra
  let D : Algebra.DescentDatum R A' E := ⟨δ, hcounit, hcoassoc⟩
  let D₀ : Subalgebra R E := D.descended
  let ε : A' ⊗[R] D₀ ≃ₐ[A'] E := D.descendedEquiv
  have ε_tmul : ∀ (a : A') (x : D₀), ε (a ⊗ₜ x) = a • (x : E) := fun a x ↦ by
    change D.descendedEquiv (a ⊗ₜ x) = _
    rw [D.descendedEquiv_apply, D.descendedMap_tmul]
  -- the affine scheme `N = Spec D₀` and the pullback square `Spec E = N ×_S W`
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap R A'))
      (CommRingCat.ofHom (algebraMap R D₀)) (CommRingCat.ofHom (algebraMap A' E))
      (CommRingCat.ofHom (algebraMap D₀ E)) := by
    refine (CommRingCat.isPushout_tensorProduct R A' D₀).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ε.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext a
      simp [ε_tmul, Algebra.smul_def]
    · ext x
      simp [ε_tmul]
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hiso : IsPullback W.isoSpec.inv (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      p S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality p).symm⟩
  have hQ := hsq.paste_horiz hiso
  have hjw : V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ W.isoSpec.inv =
      v := by
    rw [← Category.assoc]
    change V.toSpecΓ ≫ Spec.map v.appTop ≫ W.isoSpec.inv = v
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  have hV : IsPullback V.toSpecΓ v (Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫
      W.isoSpec.inv) (𝟙 W) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hjw]⟩
  refine ⟨Spec (.of D₀), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R D₀)) ≫ S.isoSpec.inv,
    V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap D₀ E)), ?_, ?_⟩
  · simpa using hV.paste_horiz hQ.flip
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc (pullback.fst _ _),
    Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  have hx := D.δ_of_mem_descended x.2
  have := δ_apply x
  rw [hx, ξ_tmul, map_one, one_mul] at this
  exact this.symm

end AlgebraicGeometry
