/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinDeformationTestCategory
import WeilConjectures.CategoryTheory.ProductPreservingVectorFunctorLinearization
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Tangent spaces and square-zero parameter algebras

Source: Stacks Project, Formal Deformation Theory, Tag 06IH, together with
Tags 06J7 and 06I0 (blueprint: lem-sfb-artin-rs-tangent-tensor).

The statement records the canonical square-zero transport and the tensor
identification of the isomorphism-class tangent functor. The proof is
intentionally postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
  [Algebra R k] [Algebra.FiniteType R k]

/-- The residue-preserving map `(a,v) ↦ (a,f v)` between square-zero test algebras.
Source: Stacks, Tag 06IG and the functor preceding Tag 06IA
(blueprint: lem-sfb-artin-rs-tangent-tensor). -/
def squareZeroMap {V W : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (f : V →ₗ[k] W) :
    squareZeroTest (R := R) (k := k) V ⟶ squareZeroTest (R := R) (k := k) W := by
  letI : Module kᵐᵒᵖ V := Module.compHom V (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k V := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k V) := Algebra.restrictScalars R k _
  letI : IsScalarTower R k (TrivSqZeroExt k V) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := k) (A := TrivSqZeroExt k V) rfl
  letI : Module kᵐᵒᵖ W := Module.compHom W (RingEquiv.toOpposite k).symm.toRingHom
  letI : IsCentralScalar k W := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra R (TrivSqZeroExt k W) := Algebra.restrictScalars R k _
  letI : IsScalarTower R k (TrivSqZeroExt k W) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := k) (A := TrivSqZeroExt k W) rfl
  let gk : TrivSqZeroExt k V →ₐ[k] TrivSqZeroExt k W := TrivSqZeroExt.map f
  let g : TrivSqZeroExt k V →ₐ[R] TrivSqZeroExt k W :=
    { toRingHom := gk.toRingHom
      commutes' := by
        intro r
        rw [IsScalarTower.algebraMap_apply R k (TrivSqZeroExt k V) r,
          IsScalarTower.algebraMap_apply R k (TrivSqZeroExt k W) r]
        exact gk.commutes (algebraMap R k r) }
  apply ObjectProperty.homMk
  refine Over.homMk (CommAlgCat.ofHom g) ?_
  ext x
  change TrivSqZeroExt.fst (gk x) = TrivSqZeroExt.fst x
  simp [gk]

/-- Transport on isomorphism classes along the actual pushforward functor.
Source: Stacks, Tag 06I0, associated functor of a predeformation category
(blueprint: lem-sfb-artin-rs-tangent-tensor). -/
def isoClassesMap (F : CofibredGroupoids.{u, v, w} R k)
    {A B : TestCategory R k} (f : A ⟶ B) :
    isoClasses F A → isoClasses F B :=
  Quotient.map (push F f).obj (by
    intro x y h
    rcases h with ⟨i⟩
    exact ⟨(push F f).mapIso i⟩)

/-- The tangent set has its canonical vector-space structure, and square-zero
parameters identify naturally with its tensor products. The pure-tensor formula
and the normalization over `k` specify the canonical identification.
Source: Stacks, Tag 06IH, with Tags 06J7 and 06I0; tensor formula from Tag 06I8
(blueprint: lem-sfb-artin-rs-tangent-tensor).

Proof:
1. Set L(V) = π₀ F(k[V]). Square-zero maps compose, so this is a functor.
The algebra k[V] is local with maximal ideal V, and is Artinian by finite
k-dimension. The map k[U × V] → k[U] ×_k k[V] is an isomorphism.
The augmentation is surjective, so (RS) gives a groupoid equivalence with the
2-fibre product. Over the terminal groupoid F(k), an isomorphism between any
pair is unique, so its isomorphism classes are L(U) × L(V). Also L(0) is a singleton.
These are exactly the definitions of def-sfb-artin-deformation-test-category.
2. Apply lem-sfb-product-preserving-vector-functor-linearization to obtain the
canonical vector structures and linearity both on objects and on morphisms.
In particular T = L(k) has addition induced by addition of square-zero parameters
and scalar multiplication induced by ε ↦ aε.
3. The map (x,v) ↦ L(f_v)(x), where f_v(a) = av, is bilinear. The universal
property of def-weil-pbc-module-tensor-product gives Φ_V(x ⊗ v) = L(f_v)(x).
For a finite basis e_i and coordinate maps p_i its inverse is
z ↦ Σ_i L(p_i)(z) ⊗ e_i. The identities Σ_i f_{e_i}p_i = id and
v = Σ_i p_i(v)e_i show that these are inverse, including the empty basis.
4. On pure tensors L(f)Φ_V(x ⊗ v) = L(f f_v)(x) = Φ_W(x ⊗ f(v));
pure tensors generate, proving naturality. For V=k this is Φ_k(x ⊗ a)=ax.
5. A functional sends Σ_i θ_i ⊗ v_i to Σ_i f(v_i)θ_i. For any tangent vector,
use its coefficients in the basis θ_i as the prescribed values f(v_i).
For d=0 both spaces are zero, the sum is empty, and the unique functional suffices. -/
theorem artinRS_tangent_tensor
    (F : CofibredGroupoids.{u, v, w} R k)
    (hpre : IsPredeformation F) (hrs : IsRimSchlessinger F) :
    ∃ (_ : AddCommGroup (tangentSet F)) (_ : Module k (tangentSet F))
      (e : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
        TensorProduct k (tangentSet F) V ≃ isoClasses F
          (squareZeroTest (R := R) (k := k) V)),
      (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        (x : tangentSet F) (z : V),
        e V (x ⊗ₜ[k] z) = isoClassesMap F (squareZeroMap
          (LinearMap.toSpanSingleton k V z)) x) ∧
      (∀ (x : tangentSet F) (a : k), e k (x ⊗ₜ[k] a) = a • x) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (f : V →ₗ[k] W),
        isoClassesMap F (squareZeroMap f) ∘ e V =
          e W ∘ (TensorProduct.map (LinearMap.id : tangentSet F →ₗ[k] tangentSet F) f)) ∧
      (∀ (d : ℕ) (bT : Module.Basis (Fin d) k (tangentSet F)) (V : Type u)
        [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        (bV : Module.Basis (Fin d) k V) (t : tangentSet F),
        ∃ f : V →ₗ[k] k,
          isoClassesMap F (squareZeroMap f)
            (e V (∑ i : Fin d, bT i ⊗ₜ[k] bV i)) = t) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
