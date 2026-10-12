/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AssertionsTransfer

/-!
# The unconditional curve assertions for finite biproducts

Let `H ≅ ⨁ₐ Gₐ` be a finite biproduct of étale sheaves of `Λ`-modules on a `k`-scheme `X`. The
assertions `C₁, C₂, C₅, C₇, C₈` (`AlgebraicGeometry.IsCurve.Assertions`), which carry no
torsion hypothesis, hold for `H` if and only if they hold for every `Gₐ`: cohomology commutes
with finite biproducts, compatibly with the pullback maps.

## Main statements

- `AddMonoidHom.subsingleton_of_sum_comp_eq`, `AddMonoidHom.finite_of_sum_comp_eq`,
  `AddMonoidHom.surjective_of_sum_comp_eq`, `AddMonoidHom.injective_of_sum_comp_eq`: an
  abelian group which is a finite "direct sum" of groups `Bₐ` (i.e. with maps `pₐ, iₐ` and
  `∑ₐ iₐ ∘ pₐ = id`) inherits vanishing, finiteness and surjectivity/injectivity of compatible
  maps from the `Bₐ`.
- `AlgebraicGeometry.IsCurve.prime_biproduct_unconditional_iff`: the biproduct equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AddMonoidHom

variable {ι : Type*} [Fintype ι] {A A' : Type*} [AddCommGroup A] [AddCommGroup A']
  {B B' : ι → Type*} [∀ a, AddCommGroup (B a)] [∀ a, AddCommGroup (B' a)]
  (p : ∀ a, A →+ B a) (i : ∀ a, B a →+ A)

/-- An abelian group which is a finite sum of subsingleton groups is a subsingleton. -/
lemma subsingleton_of_sum_comp_eq (h : ∀ x, ∑ a, i a (p a x) = x)
    [∀ a, Subsingleton (B a)] : Subsingleton A :=
  ⟨fun x y ↦ by rw [← h x, ← h y, Subsingleton.elim (p _ x) (p _ y)]⟩

/-- An abelian group which is a finite sum of finite groups is finite. -/
lemma finite_of_sum_comp_eq (h : ∀ x, ∑ a, i a (p a x) = x) [∀ a, Finite (B a)] : Finite A :=
  Finite.of_injective (fun x a ↦ p a x) fun x y hxy ↦ by
    rw [← h x, ← h y]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [congrFun hxy a]

variable {p i}

/-- A map from a finite sum of groups which is the sum of surjective maps of the summands is
surjective. -/
lemma surjective_of_sum_comp_eq (p' : ∀ a, A' →+ B' a) (i' : ∀ a, B' a →+ A')
    (h' : ∀ y, ∑ a, i' a (p' a y) = y) (φ : A →+ A') (φ' : ∀ a, B a →+ B' a)
    (hi : ∀ a b, φ (i a b) = i' a (φ' a b)) (hφ : ∀ a, Function.Surjective (φ' a)) :
    Function.Surjective φ := fun y ↦ by
  choose b hb using fun a ↦ hφ a (p' a y)
  refine ⟨∑ a, i a (b a), ?_⟩
  rw [map_sum, ← h' y]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [hi, hb]

/-- A map from a finite sum of groups which is the sum of injective maps of the summands is
injective. -/
lemma injective_of_sum_comp_eq (h : ∀ x, ∑ a, i a (p a x) = x) (p' : ∀ a, A' →+ B' a)
    (φ : A →+ A') (φ' : ∀ a, B a →+ B' a) (hp : ∀ a x, φ' a (p a x) = p' a (φ x))
    (hφ : ∀ a, Function.Injective (φ' a)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun x hx ↦ ?_
  rw [← h x]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [(hφ a).eq_iff.1 (show φ' a (p a x) = φ' a 0 by rw [hp, hx, map_zero, map_zero]),
    map_zero]

end AddMonoidHom

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] {F G : Sheaf J AddCommGrpCat.{u}}

/-- The map induced on cohomology by a finite sum of morphisms is the sum of the induced
maps. -/
lemma H.map_sum_apply {ι : Type*} [Fintype ι] (f : ι → (F ⟶ G)) {n : ℕ} (x : H F n) :
    H.map (∑ a, f a) n x = ∑ a, H.map (f a) n x := by
  simp [H.map_apply, Abelian.Ext.mk₀_sum, Abelian.Ext.comp_sum]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

namespace IsCurve

open Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Finite biproduct equivalence for unconditional curve assertions.** Let `H ≅ ⨁ₐ Gₐ` be a
finite biproduct of constructible étale sheaves of `Λ`-modules on a `k`-scheme
`f : X ⟶ Spec k`. Then the assertions `C₁, C₂, C₅, C₇, C₈` hold for `H` if and only if they
hold for every `Gₐ`. (blueprint: `lem-pbc-f1-prime-biproduct-unconditional`) -/
theorem prime_biproduct_unconditional_iff (f : X ⟶ Spec (.of k)) {I : Type*} [Finite I]
    (G : I → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (e : H ≅ ⨁ G)
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hHc : Scheme.IsConstructibleSheaf H) :
    (VanishingAboveTwo Λ H ∧ VanishingAboveOneOfIsAffine Λ H ∧ FiniteOfIsProper Λ f H ∧
        BaseChangeOfIsProper Λ f H ∧ SurjectiveRestrictionTwo Λ H) ↔
      ∀ a, VanishingAboveTwo Λ (G a) ∧ VanishingAboveOneOfIsAffine Λ (G a) ∧
        FiniteOfIsProper Λ f (G a) ∧ BaseChangeOfIsProper Λ f (G a) ∧
        SurjectiveRestrictionTwo Λ (G a) := by
  classical
  have := Fintype.ofFinite I
  set Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  -- the projections and injections of the biproduct decomposition of `H`
  let π (a : I) : Φ.obj H ⟶ Φ.obj (G a) := Φ.map (e.hom ≫ biproduct.π G a)
  let ι (a : I) : Φ.obj (G a) ⟶ Φ.obj H := Φ.map (biproduct.ι G a ≫ e.inv)
  have hιπ (a : I) : ι a ≫ π a = 𝟙 _ := by
    simp only [ι, π, ← Φ.map_comp, Category.assoc, e.inv_hom_id_assoc, biproduct.ι_π_self,
      CategoryTheory.Functor.map_id]
  have htot : ∑ a, π a ≫ ι a = 𝟙 _ := by
    have h : ∑ a, (e.hom ≫ biproduct.π G a) ≫ biproduct.ι G a ≫ e.inv = 𝟙 H := by
      simp_rw [Category.assoc, ← Preadditive.comp_sum, ← Category.assoc,
        ← Preadditive.sum_comp, biproduct.total, Category.id_comp, e.hom_inv_id]
    simp only [π, ι, ← Φ.map_comp, ← Φ.map_sum, h, CategoryTheory.Functor.map_id]
  have hsum (q : ℕ) (x : Sheaf.H (Φ.obj H) q) :
      ∑ a, Sheaf.H.map (ι a) q (Sheaf.H.map (π a) q x) = x := by
    simp only [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_sum_apply, htot, Sheaf.H.map_id_apply]
  have hsum' {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ)
      (x : Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj (Φ.obj H)) q) :
      ∑ a, Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map (ι a)) q
        (Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map (π a)) q x) = x := by
    simp only [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_sum_apply, ← Functor.map_comp,
      ← Functor.map_sum, htot, CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]
  have hinj (a : I) (q : ℕ) := injective_H_map_of_retract (ι a) (π a) (hιπ a) q
  unfold VanishingAboveTwo VanishingAboveOneOfIsAffine FiniteOfIsProper BaseChangeOfIsProper
    SurjectiveRestrictionTwo
  constructor
  · rintro ⟨h₁, h₂, h₅, h₇, h₈⟩ a
    refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, fun q ↦ ?_, fun k' _ _ X' ιk f' ι' h q ↦ ?_,
      fun {W} b _ ↦ ?_⟩
    · have := h₁ q hq
      exact (hinj a q).subsingleton
    · have := h₂ q hq
      exact (hinj a q).subsingleton
    · have := hHc
      have := h₅ q
      exact Finite.of_injective _ (hinj a q)
    · exact bijective_cohomologyMap_of_retract ι' (ι a) (π a) (hιπ a) q (h₇ k' h q)
    · exact surjective_cohomologyMap_of_retract b (ι a) (π a) (hιπ a) 2 (h₈ b)
  · intro hG
    refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, fun q ↦ ?_, fun k' _ _ X' ιk f' ι' h q ↦ ?_,
      fun {W} b _ ↦ ?_⟩
    · have (a : I) := (hG a).1 q hq
      exact AddMonoidHom.subsingleton_of_sum_comp_eq (fun a ↦ Sheaf.H.map (π a) q)
        (fun a ↦ Sheaf.H.map (ι a) q) (hsum q)
    · have (a : I) := (hG a).2.1 q hq
      exact AddMonoidHom.subsingleton_of_sum_comp_eq (fun a ↦ Sheaf.H.map (π a) q)
        (fun a ↦ Sheaf.H.map (ι a) q) (hsum q)
    · have (a : I) : Finite (Sheaf.H (Φ.obj (G a)) q) := by
        have := hGc a
        exact (hG a).2.2.1 q
      exact AddMonoidHom.finite_of_sum_comp_eq (fun a ↦ Sheaf.H.map (π a) q)
        (fun a ↦ Sheaf.H.map (ι a) q) (hsum q)
    · refine ⟨AddMonoidHom.injective_of_sum_comp_eq (hsum q)
        (fun a ↦ Sheaf.H.map ((ι')^*[AddCommGrpCat.{u + 1}].map (π a)) q)
        (cohomologyMap ι' (Φ.obj H) q) (fun a ↦ cohomologyMap ι' (Φ.obj (G a)) q)
        (fun a x ↦ cohomologyMap_map ι' q (π a) x)
        (fun a ↦ ((hG a).2.2.2.1 k' h q).1),
        AddMonoidHom.surjective_of_sum_comp_eq _ _ (hsum' ι' q)
        (cohomologyMap ι' (Φ.obj H) q) (fun a ↦ cohomologyMap ι' (Φ.obj (G a)) q)
        (fun a x ↦ cohomologyMap_map ι' q (ι a) x)
        (fun a ↦ ((hG a).2.2.2.1 k' h q).2)⟩
    · exact AddMonoidHom.surjective_of_sum_comp_eq _ _ (hsum' b 2)
        (cohomologyMap b (Φ.obj H) 2) (fun a ↦ cohomologyMap b (Φ.obj (G a)) 2)
        (fun a x ↦ cohomologyMap_map b 2 (ι a) x)
        (fun a ↦ (hG a).2.2.2.2 b)

end IsCurve

end AlgebraicGeometry
