/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.SixFunctors.NearbyCycles.ActionTrivialModEll
public import WeilConjectures.Mathlib.Topology.Algebra.Group.PowSurjective

/-!

# Generic automorphisms acting trivially modulo `ℓ`

Let `M''` be a base change model of a trait model `M` and `P'` the group of generic automorphisms
(`NearbyCyclesModel.GenericAut`) acting on `Ψ_{M''}` (`NearbyCyclesModel.baseChangeAut`). For a
complex `A` killed by `ℓ ^ m` (e.g. with `𝒪_E / ℓ ^ m`-coefficients) and its reduction
`A ⟶ Z` modulo `ℓ`, the cone of `ℓ • 𝟙 A`: if every element of `P'` is an `ℓ ^ m`-th power (`P'`
is pro-`p`, `p ≠ ℓ`, `exists_pow_eq_of_forall_nhds_one`), then a normal subgroup `V` of finite
index of `P'` acting trivially on `Ψ_{M''} Z` acts trivially on `Ψ_{M''} A`
(`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished`).

This is the step of the finiteness of the action of `P'` on `ℚ̄_ℓ`-nearby cycles (SGA 4½,
[Th. finitude], §3.7) which makes the subgroup `V`, obtained from the finiteness of the
endomorphisms of `Ψ_{M''} Z`
(`NearbyCyclesModel.exists_finiteIndex_autAction_eq_id_of_finite`), independent of the level
`m`.

-/


@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The action of the generic automorphisms on `Ψ_{M''} A`, as a homomorphism to the
endomorphism monoid. -/
noncomputable def baseChangeAutActionHom
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    GenericAut k' K →* End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A) where
  toFun σ := (baseChangeAut hM b hb v hv σ).autAction Λ A
  map_one' := autAction_baseChangeAut_one hM b hb v hv Λ A
  map_mul' σ τ := by
    rw [End.mul_def]
    exact autAction_baseChangeAut_mul hM b hb v hv Λ σ τ A

@[simp]
lemma baseChangeAutActionHom_apply
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (σ : GenericAut k' K) :
    baseChangeAutActionHom hM b hb v hv Λ A σ = (baseChangeAut hM b hb v hv σ).autAction Λ A :=
  rfl

/-- **Generic automorphisms trivial modulo `ℓ` are trivial**: let `A` be killed by `ℓ ^ m`,
`A --ℓ--> A ⟶ Z ⟶ A⟦1⟧` a distinguished triangle, and suppose every generic automorphism is an
`ℓ ^ m`-th power. Then every element of a normal subgroup `V` of finite index acting trivially on
`Ψ_{M''} Z` acts trivially on `Ψ_{M''} A`. -/
theorem autAction_baseChangeAut_eq_id_of_distinguished {ℓ m : ℕ}
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (π : A ⟶ Z) (δ : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _) (hℓ : (ℓ ^ m) • 𝟙 A = 0)
    (hdiv : ∀ σ : GenericAut k' K, ∃ τ, τ ^ ℓ ^ m = σ) (V : Subgroup (GenericAut k' K))
    [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ Z = 𝟙 _) {σ : GenericAut k' K}
    (hσ : σ ∈ V) : (baseChangeAut hM b hb v hv σ).autAction Λ A = 𝟙 _ := by
  let Ψ := (baseChange hM b hb v hv).nearbyCycles Λ
  have hT' := Ψ.map_distinguished _ hT
  have hℓ' : (ℓ ^ m) • 𝟙 (Ψ.obj A) = 0 := by
    rw [← Ψ.map_id, ← Functor.map_nsmul, hℓ, Functor.map_zero]
  let ρ := (baseChangeAutActionHom hM b hb v hv Λ A).comp V.subtype
  have hρ : ∀ τ : V, ρ τ ≫ Ψ.map π = Ψ.map π := fun τ ↦
    (Hom.autAction_naturality _ _ π).trans
      (by rw [Subgroup.coe_subtype, hV _ τ.2, Category.comp_id])
  have hπ : ∀ f : End (Ψ.obj A), f ≫ Ψ.map π = 0 → ∃ g : End (Ψ.obj A), f = ℓ • g := by
    intro f hf
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT' f hf
    let g' : Ψ.obj A ⟶ Ψ.obj A := g
    have hg' : f = g' ≫ Ψ.map (ℓ • 𝟙 A) := hg
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.comp_nsmul,
      Category.comp_id] at hg'
    exact ⟨g', hg'⟩
  have hdivV : ∀ τ : V, ∃ τ' : V, τ' ^ ℓ ^ m = τ := fun τ ↦ by
    obtain ⟨τ', hτ', h⟩ := V.exists_mem_pow_eq_of_forall_exists_pow hdiv τ.2
    exact ⟨⟨τ', hτ'⟩, Subtype.ext (by rw [Subgroup.coe_pow]; exact h)⟩
  have key := @CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow _ _ _ (Ψ.obj A)
    (Ψ.obj Z) (Ψ.map π) ℓ m hℓ' hπ V _ ρ hρ hdivV ⟨σ, hσ⟩
  rw [MonoidHom.comp_apply, baseChangeAutActionHom_apply, End.one_def] at key
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
