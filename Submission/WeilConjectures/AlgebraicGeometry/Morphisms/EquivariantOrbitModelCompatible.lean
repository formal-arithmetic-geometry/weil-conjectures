/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- An orbit model using the representatives of the supplied fixed orbit datum.

Source: Stacks Project, Tag 03SF, finite group actions on split covers; the following
is the elementary equivariant-function calculation underlying the project's orbit model.

Proof: take m = D.m and K = D.stabilizer, so the compatibility witness is the identity
of Fin D.m with reflexive subgroup equalities. Use hD to identify D.action with α.
Evaluation at D.representative(k) sends an equivariant function f to a K(k)-fixed
value: for g in K(k), equivariance and D.stabilizer_spec give
ρ(g)(f(D.representative(k))) = f(D.representative(k)). Evaluation is an H-algebra
homomorphism because all operations are coordinatewise.

For its inverse, D.complete and D.rel_spec give, for each i, an index k and g with
α(g)(D.representative(k)) = i. For a family x of fixed values set f(i) = ρ(g)(x(k)).
The index k is unique: two representatives reaching i lie in the same orbit, so
D.distinct identifies their indices. If g and g' both reach i from the same
representative, g'⁻¹*g stabilizes it. Hence x(k) is fixed by ρ(g'⁻¹*g); applying ρ(g')
and using hρmul gives ρ(g)(x(k)) = ρ(g')(x(k)). Thus the formula is independent of
the transporter. To check equivariance for a, use the transporter a*g for α(a)(i)
and hρmul. At a representative, any chosen transporter stabilizes that representative,
so f takes the prescribed fixed value there. Conversely, an equivariant function is
recovered everywhere from its representative values by the same equivariance equation.
Evaluation is therefore bijective, yielding the required H-algebra equivalence.
This does not require ρ(1) = id: 1 belongs to each stabilizer, so each fixed value
already satisfies ρ(1)(x) = x. No finiteness assumption on G is needed. For d = 0,
the representative function forces D.m = 0 and both sides are singleton algebras.
(blueprint: lem-sbc-fixed-orbit-product-equiv-compatible-model) -/
theorem equivariant_orbit_model_compatible
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) (D : FixedOrbitData G d)
    (hD : D.action = α) :
    ∃ (m : ℕ) (K : Fin m → Subgroup G),
      Nonempty ((affineTorsorEquivariantAlgebra H C G ρ d α) ≃ₐ[H]
        (∀ k : Fin m,
          (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C))) ∧
      ∃ e : Fin m ≃ Fin D.m, ∀ k, K k = D.stabilizer (e k) := by
  classical
  let m := D.m
  let r := D.representative
  let K := D.stabilizer
  have hr (i : Fin d) : ∃ k : Fin m, ∃ a : G, α a (r k) = i := by
    obtain ⟨k, hk⟩ := D.complete i
    obtain ⟨a, ha⟩ := (D.rel_spec _ _).mp hk
    exact ⟨k, a, by simpa only [hD] using ha⟩
  choose o t ht using hr
  have hor (k : Fin m) : o (r k) = k := by
    apply D.distinct
    apply (D.rel_spec _ _).mpr
    exact ⟨t (r k), by simpa only [hD] using ht (r k)⟩
  have ho (a : G) (i : Fin d) : o (α a i) = o i := by
    apply D.distinct
    apply (D.rel_spec _ _).mpr
    refine ⟨(t i)⁻¹ * a⁻¹ * t (α a i), ?_⟩
    simp only [hD, map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [ht]
    change (α (t i)).symm ((α a).symm ((α a) i)) = r (o i)
    rw [(α a).symm_apply_apply]
    exact (α (t i)).symm_apply_eq.mpr (ht i).symm
  let A := affineTorsorEquivariantAlgebra H C G ρ d α
  let B := ∀ k : Fin m,
    (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  have hA (f : Fin d → C) : f ∈ A ↔ ∀ a i, ρ a (f i) = f (α a i) := by
    simp [A, affineTorsorEquivariantAlgebra, Algebra.mem_iInf]
  have hB (k : Fin m) (x : C) :
      x ∈ (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C)) ↔
        ∀ a : G, α a (r k) = r k → ρ a x = x := by
    simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro h a ha
      exact h ⟨a, (D.stabilizer_spec k a).mpr (by simpa only [hD] using ha)⟩
    · intro h a
      exact h a.val (by simpa only [hD] using (D.stabilizer_spec k a.val).mp a.property)
  let ev : A →ₐ[H] B :=
    AlgHom.pi fun k ↦
      { toFun := fun f ↦ ⟨f.val (r k), (hB k _).mpr fun a ha ↦ by
          rw [(hA f.val).mp f.property a (r k), ha]⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
  have htransport (b : B) (k : Fin m) (a a' : G)
      (heq : α a (r k) = α a' (r k)) : ρ a (b k).val = ρ a' (b k).val := by
    have hs : α (a'⁻¹ * a) (r k) = r k := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      rw [heq]
      exact (α a').symm_apply_apply _
    have hx := (hB k _).mp (b k).property (a'⁻¹ * a) hs
    have hx' := congrArg (ρ a') hx
    simpa only [← AlgHom.comp_apply, ← hρmul, mul_inv_cancel_left] using hx'
  have hsurj : Function.Surjective ev := by
    intro b
    let f : Fin d → C := fun i ↦ ρ (t i) (b (o i)).val
    have hf : f ∈ A := by
      apply (hA f).mpr
      intro a i
      change ρ a (ρ (t i) (b (o i)).val) = ρ (t (α a i)) (b (o (α a i))).val
      rw [ho, ← AlgHom.comp_apply, ← hρmul]
      apply htransport
      rw [map_mul, Equiv.Perm.mul_apply, ht, ← ho a i, ht]
    refine ⟨⟨f, hf⟩, ?_⟩
    apply funext
    intro k
    apply Subtype.ext
    change ρ (t (r k)) (b (o (r k))).val = (b k).val
    rw [hor]
    have hs : α (t (r k)) (r k) = r k := by simpa only [hor] using ht (r k)
    exact (hB k _).mp (b k).property _ hs
  have hinj : Function.Injective ev := by
    intro f f' heq
    apply Subtype.ext
    funext i
    have h := congrArg (fun b : B ↦ (b (o i)).val) heq
    change f.val (r (o i)) = f'.val (r (o i)) at h
    rw [← ht i, ← (hA f.val).mp f.property, ← (hA f'.val).mp f'.property, h]
  exact ⟨m, K, ⟨AlgEquiv.ofBijective ev ⟨hinj, hsurj⟩⟩,
    Equiv.refl _, fun _ ↦ rfl⟩


end AlgebraicGeometry.Scheme
