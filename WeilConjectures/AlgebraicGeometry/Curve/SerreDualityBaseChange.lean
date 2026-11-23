/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality

/-!
# Serre duality and extension of the base field

Let `X` be a smooth proper curve over a field `k` with `ω = Ω¹_{X/k}`. A *Serre duality trace* is
a linear form `t : H¹(X, ω) → k` such that the pairing `Hom(M, ω) → H¹(X, M)^∨`,
`φ ↦ t ∘ H¹(φ)`, is bijective for every finite locally free `M`. By the Yoneda lemma, Serre
duality (`AlgebraicGeometry.Scheme.serreDuality`) provides such a trace, and every natural
isomorphism `H¹(X, -)^∨ ≅ Hom(-, ω)` is given by one.

For a field extension `K/k` with `X_K = X ×_k K` and an identification `ω_{X/k}|_{X_K} ≅ ω_{X_K/K}`,
the scalar extension of a Serre duality trace of `X`, composed with flat base change
`H¹(X_K, ω_{X_K}) ≅ K ⊗_k H¹(X, ω)`, is a Serre duality trace of `X_K`: the Serre duality pairing
of `M|_{X_K}` is obtained from that of `M` by extension of scalars.

## Main definitions

- `AlgebraicGeometry.Scheme.IsSerreDualityTrace`: Serre duality traces.

## Main statements

- `AlgebraicGeometry.Scheme.exists_isSerreDualityTrace`: a smooth proper curve has a Serre duality
  trace.
- `AlgebraicGeometry.Scheme.IsSerreDualityTrace.baseChange`: Serre duality commutes with
  extension of the base field.

## Implementation details

To see that the scalar extension `t'` of a trace `t` is a trace on `X_K`, choose any trace `t''`
of `X_K`. Then `t' = t'' ∘ H¹(α)` for an endomorphism `α` of `ω_{X_K}`, and the pairing of `t'`
is that of `t''` precomposed with `α`. It is bijective on `ω_{X_K} ≅ ω_{X/k}|_{X_K}` by flat base
change, so `α` is an isomorphism, and hence the pairing of `t'` is bijective everywhere.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A linear form `t : H¹(X, Ω¹_{X/k}) → k` is a **Serre duality trace** if for every finite
locally free `𝒪_X`-module `M` the pairing `Hom(M, Ω¹_{X/k}) → H¹(X, M)^∨`, `φ ↦ t ∘ H¹(φ)`, is
bijective. -/
def IsSerreDualityTrace (t : Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1)) :
    Prop :=
  ∀ M : X.Modules, M.IsFiniteLocallyFree → Function.Bijective (Modules.dualPairing t M)

/-- On a smooth curve, `Ω¹_{X/k}` is finite locally free. -/
lemma isFiniteLocallyFree_relativeDifferentials [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] :
    (X ↘ Spec (.of k)).relativeDifferentials.IsFiniteLocallyFree := by
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  exact SheafOfModules.IsInvertible.isFiniteLocallyFree _

/-- **Serre duality traces exist.** A smooth proper curve `X` over `k` has a Serre duality trace
`t : H¹(X, Ω¹_{X/k}) → k`. -/
theorem exists_isSerreDualityTrace [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    ∃ t : Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1), IsSerreDualityTrace t := by
  let ω := (X ↘ Spec (.of k)).relativeDifferentials
  let P := SheafOfModules.isFiniteLocallyFree X.ringCatSheaf
  obtain ⟨D⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules ω
  -- `H¹(X, -)^∨ ≅ Hom(-, ω)` on finite locally free modules
  let E : P.ι.op ⋙ (Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      P.ι.op ⋙ (SheafOfModules.homFunctor X.sheaf).flip.obj ω ⋙
        Modules.cohomologyFunctor k 0 :=
    D ≪≫ Functor.isoWhiskerLeft P.ι.op
      (Functor.isoWhiskerRight (Modules.dualTensorHomIso ω) (Modules.cohomologyFunctor k 0))
  let Ω : P.FullSubcategory := ⟨ω, isFiniteLocallyFree_relativeDifferentials⟩
  -- the trace is the image of `𝟙 ω`
  refine ⟨(E.inv.app (op Ω)).hom ((Modules.homObjHZeroAddEquiv ω ω).symm (𝟙 ω)),
    fun M hM ↦ ?_⟩
  let 𝓜 : P.FullSubcategory := ⟨M, hM⟩
  have key : ⇑(Modules.dualPairing ((E.inv.app (op Ω)).hom
      ((Modules.homObjHZeroAddEquiv ω ω).symm (𝟙 ω))) M) =
      (E.inv.app (op 𝓜)).hom ∘ (Modules.homObjHZeroAddEquiv M ω).symm := by
    funext φ
    have h := congrArg (fun g ↦ g.hom ((Modules.homObjHZeroAddEquiv ω ω).symm (𝟙 ω)))
      (E.inv.naturality (ObjectProperty.homMk φ : 𝓜 ⟶ Ω).op)
    dsimp at h
    refine LinearMap.ext fun x ↦ ?_
    have h' : (Modules.homObjHZeroAddEquiv M ω).symm φ =
        Modules.H.map (SheafOfModules.homObjMap (R := X.sheaf) φ (𝟙 ω)) 0
          ((Modules.homObjHZeroAddEquiv ω ω).symm (𝟙 ω)) := by
      rw [AddEquiv.symm_apply_eq, Modules.homObjHZeroAddEquiv_map]
      change φ = φ ≫ (Modules.homObjHZeroAddEquiv ω ω)
        ((Modules.homObjHZeroAddEquiv ω ω).symm (𝟙 ω))
      rw [AddEquiv.apply_symm_apply]
      exact (Category.comp_id φ).symm
    rw [Function.comp_apply, h']
    exact (LinearMap.congr_fun h x).symm
  exact (congrArg Function.Bijective key).mpr <| (E.symm.app (op 𝓜)).toLinearEquiv.bijective.comp
    (Modules.homObjHZeroAddEquiv M ω).symm.bijective

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **A form pairing perfectly on `Ω¹` is a Serre duality trace.** Let `t` be a Serre duality trace
of a smooth curve `X`. A linear form `t' : H¹(X, Ω¹_{X/k}) → k` whose pairing
`End(Ω¹_{X/k}) → H¹(X, Ω¹_{X/k})^∨` is bijective is a Serre duality trace. -/
theorem IsSerreDualityTrace.of_bijective_dualPairing
    {t t' : Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1)}
    (ht : IsSerreDualityTrace t)
    (h : Function.Bijective (Modules.dualPairing t' (X ↘ Spec (.of k)).relativeDifferentials)) :
    IsSerreDualityTrace t' := by
  let ω := (X ↘ Spec (.of k)).relativeDifferentials
  have hω : ω.IsFiniteLocallyFree := isFiniteLocallyFree_relativeDifferentials
  -- `t' = t ∘ H¹(α)`
  obtain ⟨α, hα⟩ := (ht ω hω).2 t'
  have key (M : X.Modules) (φ : M ⟶ ω) :
      Modules.dualPairing t' M φ = Modules.dualPairing t M (φ ≫ α) := by
    rw [Modules.dualPairing_comp, hα]
    rfl
  -- `α` is an isomorphism
  have hinj : Function.Injective fun φ : ω ⟶ ω ↦ φ ≫ α := fun a b hab ↦
    h.1 (by rw [key, key]; exact congrArg _ hab)
  obtain ⟨β, hβ⟩ : ∃ β : ω ⟶ ω, β ≫ α = 𝟙 ω := by
    obtain ⟨β, hβ⟩ := h.2 (Modules.dualPairing t ω (𝟙 ω))
    exact ⟨β, (ht ω hω).1 (by rw [← key, hβ])⟩
  have hαβ : α ≫ β = 𝟙 ω := hinj (by
    change (α ≫ β) ≫ α = 𝟙 ω ≫ α
    rw [Category.assoc, hβ]
    exact (Category.comp_id α).trans (Category.id_comp α).symm)
  intro M hM
  have hM' : ⇑(Modules.dualPairing t' M) = Modules.dualPairing t M ∘ fun φ ↦ φ ≫ α :=
    funext (key M)
  refine (congrArg Function.Bijective hM').mpr <| (ht M hM).comp
    (Function.bijective_iff_has_inverse.2 ⟨fun φ ↦ φ ≫ β, fun φ ↦ ?_, fun φ ↦ ?_⟩)
  · change (φ ≫ α) ≫ β = φ
    rw [Category.assoc, hαβ]
    exact Category.comp_id φ
  · change (φ ≫ β) ≫ α = φ
    rw [Category.assoc, hβ]
    exact Category.comp_id φ

variable [IsProper (X ↘ Spec (.of k))] (K : Type u) [Field K] [Algebra k K]

/-- **Serre duality commutes with extension of the base field.** Let `X` be a smooth proper
curve over `k`, let `K/k` be a field extension, `X_K = X ×_k K`, and let
`c : Ω¹_{X/k}|_{X_K} ≅ Ω¹_{X_K/K}`. For every Serre duality trace `t` of `X` there is a Serre
duality trace `t'` of `X_K` such that for every `𝒪_X`-module `M` and `φ : M ⟶ Ω¹_{X/k}`, the
pairing of `t'` with `φ_K = c ∘ φ|_{X_K}`, composed with flat base change
`K ⊗_k H¹(X, M) ⟶ H¹(X_K, M|_{X_K})`, is the scalar extension of the pairing of `t` with `φ`:
the Serre duality pairing for `M|_{X_K}` is obtained from that for `M` by extension of
scalars. -/
theorem IsSerreDualityTrace.baseChange
    {t : Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1)}
    (ht : IsSerreDualityTrace t)
    (c : (Modules.pullback (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (X ↘ Spec (.of k)).relativeDifferentials ≅
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
        Spec (.of K)).relativeDifferentials) :
    ∃ t' : Module.Dual K ((pullback (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)).relativeDifferentials.H 1),
      IsSerreDualityTrace t' ∧
      ∀ (M : X.Modules) (φ : M ⟶ (X ↘ Spec (.of k)).relativeDifferentials),
        Modules.dualPairing t' _ ((Modules.pullback (pullback.fst (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map φ ≫ c.hom) ∘ₗ
          Modules.H.baseChangeField (k := k) K M 1 =
        (Modules.dualPairing t M φ).baseChange K := by
  let f := X ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ω := f.relativeDifferentials
  let ωK := (pullback f g ↘ Spec (.of K)).relativeDifferentials
  -- `X_K` is a smooth proper curve over `K`
  have hpb := IsPullback.of_hasPullback f g
  have : SmoothOfRelativeDimension 1 (pullback f g ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hpb ‹_›
  have : IsProper (pullback f g ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback hpb ‹_›
  obtain ⟨t'', ht''⟩ := exists_isSerreDualityTrace (k := K) (X := pullback f g)
  have hω : ω.IsFiniteLocallyFree := isFiniteLocallyFree_relativeDifferentials
  have hωK : ωK.IsFiniteLocallyFree := isFiniteLocallyFree_relativeDifferentials
  have : ω.IsFinitePresentation := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation _
  have : ω.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsLocallyFree _
  have : FiniteDimensional k (ω.H 1) := Modules.finiteDimensional_H_of_isProper ω 1
  -- `e : K ⊗_k H¹(X, ω) ≃ H¹(X_K, ω_K)`: flat base change followed by `c`
  let b : K ⊗[k] ω.H 1 ≃ₗ[K] ((Modules.pullback (pullback.fst f g)).obj ω).H 1 :=
    LinearEquiv.ofBijective (Modules.H.baseChangeField (k := k) K ω 1)
      (Modules.H.bijective_baseChangeField K ω 1)
  let hc : ((Modules.pullback (pullback.fst f g)).obj ω).H 1 ≃ₗ[K] ωK.H 1 :=
    { Modules.H.mapLinearEquiv c 1 with
      map_smul' := fun a x ↦
        (Modules.H.mapLinearEquiv c 1).map_smul (globalSectionsRingHom K a) x }
  let e := b.trans hc
  have he (x : ω.H 1) :
      e (1 ⊗ₜ x) = Modules.H.map c.hom 1 (Modules.H.baseChangeField (k := k) K ω 1 (1 ⊗ₜ x)) :=
    rfl
  have hnat (M : X.Modules) (φ : M ⟶ ω) (x : M.H 1) :
      Modules.H.map ((Modules.pullback (pullback.fst f g)).map φ) 1
          (Modules.H.baseChangeField (k := k) K M 1 (1 ⊗ₜ x)) =
        Modules.H.baseChangeField (k := k) K ω 1 (1 ⊗ₜ Modules.H.map φ 1 x) :=
    Modules.H.map_pullback_baseChangeField_one_tmul K φ 1 x
  let t' : Module.Dual K (ωK.H 1) := t.baseChange K ∘ₗ e.symm.toLinearMap
  have ht' (y : ωK.H 1) : t' y = t.baseChange K (e.symm y) := rfl
  -- the pairing of `t'` is the scalar extension of the pairing of `t`
  have key (M : X.Modules) (φ : M ⟶ ω) :
      Modules.dualPairing t' _ ((Modules.pullback (pullback.fst f g)).map φ ≫ c.hom) ∘ₗ
          Modules.H.baseChangeField (k := k) K M 1 =
        (Modules.dualPairing t M φ).baseChange K := by
    refine TensorProduct.AlgebraTensorModule.curry_injective
      (LinearMap.ext fun a ↦ LinearMap.ext fun x ↦ ?_)
    have hx : (a ⊗ₜ[k] x : K ⊗[k] M.H 1) = a • (1 ⊗ₜ x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.comp_apply]
    rw [Module.Dual.baseChange_apply_tmul, hx, LinearMap.map_smul, LinearMap.map_smul,
      Modules.dualPairing_apply, Modules.dualPairing_apply, Modules.H.map_comp_apply, hnat, ← he,
      ht', LinearEquiv.symm_apply_apply, Module.Dual.baseChange_apply_tmul, smul_eq_mul,
      Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm]
  refine ⟨t', ?_, key⟩
  apply IsSerreDualityTrace.of_bijective_dualPairing ht''
  -- `H¹(X_K, ω_K)` is the base change of `H¹(X, ω)`
  let : Module k (ωK.H 1) := Module.compHom _ (algebraMap k K)
  have : IsScalarTower k K (ωK.H 1) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let j : ω.H 1 →ₗ[k] ωK.H 1 :=
    (e.toLinearMap.restrictScalars k) ∘ₗ TensorProduct.mk k K (ω.H 1) 1
  have ibc : IsBaseChange K j := IsBaseChange.of_equiv e fun _ ↦ rfl
  have hpair (φ : ω ⟶ ω) : Modules.dualPairing t' ωK
      (c.inv ≫ (Modules.pullback (pullback.fst f g)).map φ ≫ c.hom) =
        ibc.toDual (Modules.dualPairing t ω φ) := by
    refine ibc.algHom_ext _ _ fun v ↦ ?_
    rw [IsBaseChange.toDual_comp_apply]
    have h := LinearMap.congr_fun (key ω φ) (1 ⊗ₜ v)
    rw [LinearMap.comp_apply, Module.Dual.baseChange_apply_tmul] at h
    change Modules.dualPairing t' ωK _
      (Modules.H.map c.hom 1 (Modules.H.baseChangeField (k := k) K ω 1 (1 ⊗ₜ v))) = _
    rw [Modules.dualPairing_apply, ← Modules.H.map_comp_apply, Iso.hom_inv_id_assoc,
      ← Modules.dualPairing_apply, h, Algebra.algebraMap_eq_smul_one]
  -- the pairing of `t'` on `ω_K` is surjective
  have hsurj : Function.Surjective (Modules.dualPairingLinearMap t' ωK) := by
    intro y
    obtain ⟨z, rfl⟩ := ibc.toDualBaseChange.surjective y
    induction z using TensorProduct.inductionOn with
    | tmul a l =>
      obtain ⟨φ, rfl⟩ := (ht ω hω).2 l
      refine ⟨a • (c.inv ≫ (Modules.pullback (pullback.fst f g)).map φ ≫ c.hom), ?_⟩
      rw [map_smul, Modules.dualPairingLinearMap_apply, hpair]
      refine ibc.algHom_ext _ _ fun v ↦ ?_
      rw [IsBaseChange.toDualBaseChange_tmul, LinearMap.smul_apply,
        IsBaseChange.toDual_comp_apply, smul_eq_mul]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨a₁, h₁⟩ := h₁
      obtain ⟨a₂, h₂⟩ := h₂
      exact ⟨a₁ + a₂, by rw [map_add, h₁, h₂, map_add]⟩
  -- and both sides have the same dimension, by Serre duality on `X_K`
  let d := LinearEquiv.ofBijective (Modules.dualPairingLinearMap t'' ωK) (ht'' ωK hωK)
  have : FiniteDimensional K (ωK.H 1) := LinearEquiv.finiteDimensional e
  have : FiniteDimensional K (ωK ⟶ ωK) := LinearEquiv.finiteDimensional d.symm
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank d.finrank_eq).2 hsurj, hsurj⟩

end AlgebraicGeometry.Scheme
