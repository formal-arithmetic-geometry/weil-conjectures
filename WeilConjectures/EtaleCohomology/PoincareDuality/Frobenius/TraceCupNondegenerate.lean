/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism

/-!
# Nondegeneracy of the trace–cup pairing at a finite level

Let `k` be separably closed, `a : X ⟶ Spec k` proper with a Tate orientation `γ` of relative
dimension `d`, and `Λ` a finite self-injective cogenerating coefficient ring (e.g. `ℤ/ℓᵐ`) whose
characteristic is invertible on `X`. Write `Hⁿ(X, Λ) = Hom(Λ_X, Λ_X[n])`. There is an additive
map `T : H^{2d}(X, Λ) ⟶ Λ` (a trace) such that for every `i + j = 2d` the trace–cup pairing
`(x, y) ↦ T(x ⌣ y)` is nondegenerate on both sides
(`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_traceCup`).

The trace is `z ↦ 1 ≫ (z ≫ γ')^♭`, where `γ' : Λ_X[2d] ≅ Ra^! Λ` is the orientation read through
`Λ(d) ≅ Λ` over the separably closed `k`, `(-)^♭` is the adjunction `Ra_! ⊣ Ra^!` and
`1 : Λ ⟶ Ra_! Λ_X` is the unit class (`AlgebraicGeometry.Etale.unitClassCompactSupport`). The cup
product is the Yoneda product `x ⌣ y = x ≫ y[i]` (`CategoryTheory.MonoidalCategory.shiftProduct_eq`),
so that `T(x ⌣ y) = (1 ≫ Ra_!(x)) ≫ (y[i] ≫ γ')^♭`: the composition pairing
`Hom(Λ, E) × Hom(E, Λ) ⟶ End(Λ)` at `E = Ra_!(Λ_X[i])`, nondegenerate at the separably closed point
(`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed_of_injective`), read through the
bijections `x ↦ 1 ≫ Ra_!(x)` (`La^* ⊣ Ra_*` and `Ra_! ≅ Ra_*`) and `y ↦ (y[i] ≫ γ')^♭`.

This is the finite-level duality of blueprint `sk-thm-transport` in the form needed for the trace–cup
structure at `ℚ̄_ℓ` (`sk-cor-trace`, `sk-thm-derived-duality`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] [HasTateTwist Λ]
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} [HasInvertibleExponent Λ X] {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [IsProper a] {d : ℕ}

namespace TateOrientation

/-- A pairing `(x, y) ↦ p x ≫ q y` through zero-preserving bijections `p : α → Hom(B, E)` and
`q : β → Hom(E, B)` is nondegenerate on both sides as soon as the composition pairing
`Hom(B, E) × Hom(E, B) ⟶ End(B)` is. -/
lemma nondegenerate_of_bijective_comp {C : Type*} [Category C] [Preadditive C] {B E : C}
    {α β : Type*} [Zero α] [Zero β] (p : α → (B ⟶ E)) (q : β → (E ⟶ B))
    (hp : Function.Bijective p) (hq : Function.Bijective q) (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (h : (∀ v : B ⟶ E, v ≠ 0 → ∃ f : E ⟶ B, v ≫ f ≠ 0) ∧
      (∀ f : E ⟶ B, f ≠ 0 → ∃ v : B ⟶ E, v ≫ f ≠ 0)) :
    (∀ x, (∀ y, p x ≫ q y = 0) → x = 0) ∧ (∀ y, (∀ x, p x ≫ q y = 0) → y = 0) := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · by_contra hne
    obtain ⟨f, hf⟩ := h.1 (p x) fun h0 ↦ hne (hp.1 (h0.trans hp0.symm))
    obtain ⟨y, rfl⟩ := hq.2 f
    exact hf (hx y)
  · by_contra hne
    obtain ⟨v, hv⟩ := h.2 (q y) fun h0 ↦ hne (hq.1 (h0.trans hq0.symm))
    obtain ⟨x, rfl⟩ := hp.2 v
    exact hv (hy x)

/-- **The trace–cup pairing is nondegenerate at a finite level.** For `a : X ⟶ Spec k` proper
over a separably closed field with a Tate orientation `γ` of relative dimension `d`, and a finite
self-injective cogenerating ring `Λ`, there is an additive map `T : H^{2d}(X, Λ) ⟶ Λ` such that,
for all `i + j = 2d`, the pairing `(x, y) ↦ T(x ⌣ y)` on `Hⁱ(X, Λ) × Hʲ(X, Λ)` is nondegenerate
on both sides. -/
theorem exists_nondegenerate_traceCup
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (γ : TateOrientation Λ a d) :
    ∃ T : (𝟙_ (DerivedCategoryModule Λ X) ⟶
        (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧) →+ Λ,
      ∀ (i j : ℤ) (hij : i + j = 2 * d),
        (∀ x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧,
          (∀ y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧,
            T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = 0) → x = 0) ∧
        (∀ y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧,
          (∀ x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧,
            T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = 0) → y = 0) := by
  obtain ⟨eT⟩ := nonempty_tateObject_iso_unit Λ k (d : ℤ)
  let eX : tateObject Λ X d ≅ 𝟙_ (DerivedCategoryModule Λ X) :=
    (leftDerivedUpperStarTateObjectIso a (d : ℤ)).symm ≪≫
      (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso eT ≪≫ leftDerivedUpperStarConstantComplexIso Λ a
  let γ' : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex _ a :=
    (shiftFunctor _ (2 * d : ℤ)).mapIso eX.symm ≪≫ γ.dualizingComplexIso
  let adj := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) a
  let eΛ := (endUnitAddEquiv Λ (Spec (.of k))).symm
  let T : (𝟙_ (DerivedCategoryModule Λ X) ⟶
      (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧) →+ Λ :=
    AddMonoidHom.mk' (fun z ↦ eΛ (unitClassCompactSupport Λ a ≫
      (adj.homEquiv _ _).symm (z ≫ γ'.hom))) fun z z' ↦ by
        rw [← map_add]
        congr 1
        simp only [Adjunction.homEquiv_counit, Preadditive.add_comp, Functor.map_add,
          Preadditive.comp_add]
  refine ⟨T, fun i j hij ↦ ?_⟩
  let p : ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) →
      (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
        (R(a)_![ModuleCat.{u + 1} Λ]).obj ((𝟙_ (DerivedCategoryModule Λ X))⟦i⟧)) :=
    fun x ↦ unitClassCompactSupport Λ a ≫ (R(a)_![ModuleCat.{u + 1} Λ]).map x
  let Φ : ((𝟙_ (DerivedCategoryModule Λ X))⟦j⟧)⟦i⟧ ≅ dualizingComplex _ a :=
    (shiftFunctorAdd' _ j i (i + j) (add_comm j i)).symm.app _ ≪≫
      eqToIso (by rw [hij]) ≪≫ γ'
  let q : ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧) →
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj ((𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) ⟶
        𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) :=
    fun y ↦ (adj.homEquiv _ _).symm (y⟦i⟧' ≫ Φ.hom)
  have key : ∀ x y, T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = eΛ (p x ≫ q y) := by
    intro x y
    show eΛ _ = eΛ _
    congr 1
    rw [cupProduct_eq_shiftProduct,
      MonoidalCategory.shiftProduct_eq (DerivedCategory.unitorsCommShift _)]
    simp only [p, q, Φ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom]
    simp only [Category.assoc]
    rw [Adjunction.homEquiv_naturality_left_symm]
  sorry

end TateOrientation

end AlgebraicGeometry.Etale
