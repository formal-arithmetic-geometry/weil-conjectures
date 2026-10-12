/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Pulling `Ext`-classes back along an exact right adjoint

Let `L ⊣ R` be an adjunction between abelian categories with `L` and `R` exact, and let
`σ : A ⟶ R B` be a morphism whose adjoint `L A ⟶ B` is an isomorphism. Then pulling classes back
along `R` and precomposing with `σ` is a bijection `Ext B G n ≃ Ext A (R G) n`.

For an étale morphism `p : W ⟶ X`, `R = p^*` and `L = p_!`, this computes the cohomology of
`W` with coefficients in `p^* G` as `Ext` out of the sheaf corepresenting sections over `W`.

## Main statements

- `CategoryTheory.Adjunction.mapExtCounit_mk₀_comp_mapExactFunctor`: the composite with
  `CategoryTheory.Adjunction.mapExtCounit` is precomposition with the adjoint of `σ`.
- `CategoryTheory.Adjunction.bijective_mk₀_comp_mapExactFunctor`: the bijectivity statement.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Adjunction

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {R : D ⥤ C} [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
  [EnoughInjectives D]

/-- Pulling a class back along `R`, precomposing with `σ : A ⟶ R B` and then applying
`CategoryTheory.Adjunction.mapExtCounit` is precomposition with the adjoint `L A ⟶ B` of `σ`. -/
lemma mapExtCounit_mk₀_comp_mapExactFunctor {A : C} {B G : D} (σ : A ⟶ R.obj B) {n : ℕ}
    (x : Ext B G n) :
    adj.mapExtCounit A G n ((Ext.mk₀ σ).comp (x.mapExactFunctor R) (zero_add n)) =
      (Ext.mk₀ ((adj.homEquiv _ _).symm σ)).comp x (zero_add n) := by
  have : PreservesFiniteLimits (R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ L) := comp_preservesFiniteColimits _ _
  rw [mapExtCounit_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_mapExactFunctor,
    Ext.mapExactFunctor_comp_mk₀_app (R ⋙ L) (𝟭 D) adj.counit x, Ext.mapExactFunctor_id,
    Ext.mk₀_comp_mk₀_assoc, adj.homEquiv_counit]

/-- For an adjunction `L ⊣ R` of exact functors and `σ : A ⟶ R B` whose adjoint `L A ⟶ B` is an
isomorphism, `x ↦ σ ∘ R(x)` is a bijection `Ext B G n ≃ Ext A (R G) n`. -/
lemma bijective_mk₀_comp_mapExactFunctor {A : C} {B : D} (σ : A ⟶ R.obj B)
    [IsIso ((adj.homEquiv _ _).symm σ)] (G : D) (n : ℕ) :
    Function.Bijective
      (fun x : Ext B G n ↦ (Ext.mk₀ σ).comp (x.mapExactFunctor R) (zero_add n)) := by
  refine ((adj.mapExtCounit_bijective A G n).of_comp_iff' _).1 ?_
  have h : (adj.mapExtCounit A G n) ∘
      (fun x : Ext B G n ↦ (Ext.mk₀ σ).comp (x.mapExactFunctor R) (zero_add n)) =
      fun x ↦ (Ext.mk₀ ((adj.homEquiv _ _).symm σ)).comp x (zero_add n) := by
    funext x
    exact adj.mapExtCounit_mk₀_comp_mapExactFunctor σ x
  rw [h]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦
    ⟨(Ext.mk₀ (inv ((adj.homEquiv _ _).symm σ))).comp y (zero_add n), ?_⟩⟩
  · have := congrArg (fun z ↦ (Ext.mk₀ (inv ((adj.homEquiv _ _).symm σ))).comp z (zero_add n))
      hxy
    simpa only [Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp] using this
  · simp only [Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id, Ext.mk₀_id_comp]

end CategoryTheory.Adjunction
