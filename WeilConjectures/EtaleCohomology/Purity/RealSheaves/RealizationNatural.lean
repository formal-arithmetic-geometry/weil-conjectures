/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RepresentationTheory.LinHom
public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization

/-!
# Natural small models of realizations, and functors between categories of representations

Complements to `WeilConjectures.RepresentationTheory.FiniteDimensionalRealization`, used for the
lisse sheaf–representation equivalence (`prop-wf-weil-sheaf-representation-equivalence`):

* `Rep.uliftFunctor`: the universe lift `Rep.{w} k G ⥤ Rep.{max w w'} k G`, `V ↦ ULift V`;
* `Rep.tprodFunctor`: the tensor product `(V, W) ↦ V ⊗ W` of representations, as a bifunctor
  (the category `Rep.{w} k G` is only monoidal in Mathlib when `w` is the universe of `k`);
* `Representation.exists_equivalence_of_realization_natural`: the small model equivalence of a
  realization, together with a *natural* identification of the underlying spaces with the
  realization;
* `Representation.Equiv.tprodEquivLinHomOfDual_map`: the naturality of the identification
  `ρ ⊗ σ ≅ Hom(ρ', σ)` for `ρ' ≅ ρ^∨`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

namespace Rep

variable (k : Type v) [CommRing k] (G : Type*) [Monoid G]

/-- The universe lift `V ↦ ULift V` of representations. -/
noncomputable def uliftFunctor : Rep.{w} k G ⥤ Rep.{max w w'} k G where
  obj X := Rep.of (X.ρ.transport (ULift.moduleEquiv (R := k) (M := X.V)).symm)
  map {X Y} f := Rep.ofHom
    ⟨(ULift.moduleEquiv (R := k) (M := Y.V)).symm.toLinearMap ∘ₗ f.hom.toLinearMap ∘ₗ
      (ULift.moduleEquiv (R := k) (M := X.V)).toLinearMap, fun g ↦ LinearMap.ext fun x ↦
        congrArg ULift.up (Rep.hom_comm_apply f g x.down)⟩
  map_id _ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))
  map_comp _ _ :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))

lemma uliftFunctor_map_hom_apply {X Y : Rep.{w} k G} (f : X ⟶ Y) (x : ULift.{w'} X.V) :
    ((uliftFunctor.{w, w'} k G).map f).hom x = ULift.up (f.hom x.down) :=
  rfl

/-- The tensor product of representations, as a bifunctor. -/
noncomputable def tprodFunctor :
    Rep.{max v w} k G × Rep.{max v w} k G ⥤ Rep.{max v w} k G where
  obj X := Rep.of (X.1.ρ.tprod X.2.ρ)
  map f := Rep.ofHom (f.1.hom.tensor f.2.hom)
  map_id _ := Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ ↦ rfl))
  map_comp _ _ :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ ↦ rfl))

lemma tprodFunctor_map_hom_tmul {X Y : Rep.{max v w} k G × Rep.{max v w} k G} (f : X ⟶ Y)
    (x : X.1.V) (y : X.2.V) :
    ((tprodFunctor.{w} k G).map f).hom (x ⊗ₜ y) = f.1.hom x ⊗ₜ f.2.hom y :=
  rfl

end Rep

namespace Representation

open Module Realization

/-- **Natural small model of a realization.** The equivalence of
`Representation.exists_equivalence_of_realization` between a category `A`, realized by
finite-dimensional representations `ρ X` on `V X`, and finite-dimensional representations in
`Rep.{u} k G` continuous along `ι`, comes with identifications `f X` of the underlying spaces
with `V X` which intertwine the representations and are natural in `X`. -/
theorem exists_equivalence_of_realization_natural
    {k : Type} [Field k] [TopologicalSpace k] {G : Type u} [Group G] {H : Type*} [Group H]
    [TopologicalSpace H] (ι : H →* G) {A : Type*} [Category A]
    (V : A → Type (u + 1)) [∀ X, AddCommGroup (V X)] [∀ X, Module k (V X)]
    [∀ X, FiniteDimensional k (V X)]
    (ρ : ∀ X, Representation k G (V X)) (hρ : ∀ X, (ρ X).IsContinuousOn ι)
    (map : ∀ {X Y : A}, (X ⟶ Y) → (V X →ₗ[k] V Y))
    (map_id : ∀ X, map (𝟙 X) = LinearMap.id)
    (map_comp : ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map g ∘ₗ map f)
    (map_comm : ∀ {X Y : A} (f : X ⟶ Y) (g : G) (v : V X), map f (ρ X g v) = ρ Y g (map f v))
    (faithful : ∀ {X Y : A} (f f' : X ⟶ Y), map f = map f' → f = f')
    (full : ∀ {X Y : A} (φ : V X →ₗ[k] V Y), (∀ g v, φ (ρ X g v) = ρ Y g (φ v)) →
      ∃ f : X ⟶ Y, map f = φ)
    (essSurj : ∀ (V' : Type (u + 1)) [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (ρ' : Representation k G V'), ρ'.IsContinuousOn ι →
        ∃ (X : A) (e : V X ≃ₗ[k] V'), ∀ g v, e (ρ X g v) = ρ' g (e v))
    (Q : ObjectProperty (Rep.{u} k G))
    (hQ : ∀ X : Rep.{u} k G, Q X ↔ FiniteDimensional k X.V ∧ X.ρ.IsContinuousOn ι) :
    ∃ (e : A ≌ Q.FullSubcategory) (f : ∀ X : A, (e.functor.obj X).obj.V ≃ₗ[k] V X),
      (∀ X g v, f X ((e.functor.obj X).obj.ρ g v) = ρ X g (f X v)) ∧
      ∀ {X Y : A} (φ : X ⟶ Y) v, f Y ((e.functor.map φ).hom.hom v) = map φ (f X v) := by
  let b := basisEquiv k V
  let F : A ⥤ Q.FullSubcategory :=
    { obj X := ⟨Rep.of ((ρ X).transport (b X)),
        (hQ _).2 ⟨LinearEquiv.finiteDimensional (b X),
          (hρ X).of_linearEquiv (b X) fun g v ↦ apply_transport _ _ _ _⟩⟩
      map {X Y} f := ObjectProperty.homMk <| Rep.ofHom
        ⟨(b Y).toLinearMap ∘ₗ map f ∘ₗ (b X).symm.toLinearMap, fun g ↦
          LinearMap.ext fun w ↦ by simp [map_comm]⟩
      map_id X := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
        IntertwiningMap.ext <| LinearMap.ext fun w ↦ by simp [map_id]
      map_comp f g := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
        IntertwiningMap.ext <| LinearMap.ext fun w ↦ by simp [map_comp] }
  have hF : F.IsEquivalence :=
    { faithful := ⟨fun {X Y} f f' hff' ↦ faithful f f' <| LinearMap.ext fun v ↦ by
        have := congr($(hff').hom.hom (b X v))
        simpa [F] using this⟩
      full := ⟨fun {X Y} φ ↦ by
        obtain ⟨f, hf⟩ := full ((b Y).symm.toLinearMap ∘ₗ φ.hom.hom.toLinearMap ∘ₗ
          (b X).toLinearMap) fun g v ↦ by
            have := Rep.hom_comm_apply φ.hom g (b X v)
            change φ.hom.hom ((ρ X).transport (b X) g (b X v)) =
              (ρ Y).transport (b Y) g (φ.hom.hom (b X v)) at this
            simp only [transport_apply, LinearEquiv.symm_apply_apply] at this
            exact (congrArg (b Y).symm this).trans ((b Y).symm_apply_apply _)
        refine ⟨f, ObjectProperty.hom_ext _ <| Rep.hom_ext <|
          IntertwiningMap.ext <| LinearMap.ext fun w ↦ ?_⟩
        simp [F, hf]⟩
      essSurj := ⟨fun Y ↦ by
        have := ((hQ _).1 Y.property).1
        let ρ' : Representation k G (ULift.{u + 1} Y.obj.V) :=
          Y.obj.ρ.transport ULift.moduleEquiv.symm
        have : FiniteDimensional k (ULift.{u + 1} Y.obj.V) :=
          LinearEquiv.finiteDimensional ULift.moduleEquiv.symm
        obtain ⟨X, e, he⟩ := essSurj (ULift.{u + 1} Y.obj.V) ρ'
          (((hQ _).1 Y.property).2.of_linearEquiv _ fun g v ↦ apply_transport _ _ _ _)
        let e' : ((ρ X).transport (b X)).Equiv Y.obj.ρ :=
          .mk ((b X).symm ≪≫ₗ e ≪≫ₗ ULift.moduleEquiv) fun g ↦ LinearMap.ext fun w ↦ by
            have := he g ((b X).symm w)
            simp only [ρ', transport_apply] at this
            simp [this]
        exact ⟨X, ⟨ObjectProperty.isoMk _ (Rep.mkIso e')⟩⟩⟩ }
  refine ⟨F.asEquivalence, fun X ↦ (b X).symm, fun X g v ↦ (b X).symm_apply_apply _,
    fun {X Y} φ v ↦ ?_⟩
  exact (b Y).symm_apply_apply _

variable {k G V V' W W₂ V₂ V₂' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W] [Module k W] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₂'] [Module k V₂'] [AddCommGroup W₂] [Module k W₂]
  {ρ : Representation k G V} {ρ' : Representation k G V'} {σ : Representation k G W}
  {ρ₂ : Representation k G V₂} {ρ₂' : Representation k G V₂'} {σ₂ : Representation k G W₂}

/-- The identification `ρ ⊗ σ ≅ Hom(ρ', σ)` sends `v ⊗ w` to `d ↦ b(d)(v) • w`. -/
lemma Equiv.tprodEquivLinHomOfDual_tmul [FiniteDimensional k V] (b : ρ'.Equiv ρ.dual) (v : V)
    (w : W) (d : V') :
    Equiv.tprodEquivLinHomOfDual (σ := σ) b (v ⊗ₜ w) d = b d v • w :=
  rfl

/-- **Naturality of `ρ ⊗ σ ≅ Hom(ρ', σ)`**: for linear maps `α : V → V₂`, `β : W → W₂` and
`γ : V₂' → V'` such that `γ` is dual to `α` under `ρ' ≅ ρ^∨` and `ρ₂' ≅ ρ₂^∨`, the identification
sends `(α ⊗ β) x` to `β ∘ x ∘ γ`. -/
lemma Equiv.tprodEquivLinHomOfDual_map [FiniteDimensional k V] [FiniteDimensional k V₂]
    (b : ρ'.Equiv ρ.dual) (b₂ : ρ₂'.Equiv ρ₂.dual) (α : V →ₗ[k] V₂) (β : W →ₗ[k] W₂)
    (γ : V₂' →ₗ[k] V') (h : ∀ d v, b (γ d) v = b₂ d (α v)) (x : TensorProduct k V W) :
    Equiv.tprodEquivLinHomOfDual (σ := σ₂) b₂ (TensorProduct.map α β x) =
      β ∘ₗ Equiv.tprodEquivLinHomOfDual (σ := σ) b x ∘ₗ γ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    ext d
    simp only [TensorProduct.map_tmul, LinearMap.comp_apply, tprodEquivLinHomOfDual_tmul, h,
      map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp, LinearMap.comp_add]

end Representation
