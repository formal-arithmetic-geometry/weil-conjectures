/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Dualizability detected by jointly conservative closed monoidal functors

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 4.5, proof
(blueprint: lem-zl-dualizable-jointly-conservative-locality).
-/

@[expose] public section

universe w u v u' v'

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory

/-- Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 4.5, proof
(blueprint: lem-zl-dualizable-jointly-conservative-locality).
A jointly conservative family of strong symmetric monoidal functors preserving internal Hom
and transposes detects dualizable objects, including for an empty or infinite family.

Mathlib curries `B ⊗ A ⟶ T`; the transpose of `g : A ⊗ B ⟶ T` below is therefore
`curry ((β_ B A).hom ≫ g)`. This transports the chosen closed structure through the symmetry.
The natural isomorphisms `h i B` are natural in the target; `hHomNaturality` supplies their
naturality in the contravariant argument. An exact pairing `ExactPairing K E` is precisely
evaluation `E ⊗ K ⟶ 𝟙_ C`, coevaluation `𝟙_ C ⟶ K ⊗ E`, and the two triangles.

Proof plan:
1. Transport a dual pair through each strong monoidal functor, using its unit and tensor
isomorphisms. Naturality and monoidal coherence identify both transported triangles with the
images of the original triangles.
2. Put `D = [K, 𝟙]`, with evaluation the inverse transpose of its identity. Define
`φ M : M ⊗ D ⟶ [K, M]` by transposing the composite that evaluates `D ⊗ K`, then uses
`M ⊗ 𝟙 ≅ M`. Naturality gives the usual inverse-transpose formula.
3. When `F i K` has a dual `E`, use `lem-sfb-dual-tensor-adjunctions` to obtain
`- ⊗ F i K ⊣ - ⊗ E`. Its counit is evaluation on `E ⊗ F i K`. By
`det-sp-unique-right-adjoint`, compare it with internal Hom. At the unit this identifies
`E` with `[F i K, 𝟙]` compatibly with evaluation; at every object it shows the corresponding
canonical comparison `φ` is invertible.
4. Compose `h i K` at the unit with internal Hom of the inverse unit comparison. This gives
an isomorphism `F i D ≅ [F i K, 𝟙]`. Transpose compatibility applied to evaluation, and
naturality in the unit comparison, identify its evaluation with transported evaluation.
5. Take inverse transposes to compare `h i K` composed with `F i (φ M)` and its tensorator
with the target-category canonical comparison composed with `1 ⊗ (F i D ≅ [F i K, 𝟙])`.
Tensorator naturality, associativity and right-unit coherence give exactly this equality.
6. The target comparison is invertible by step 3; all the other comparison factors are
invertible by step 4 and the hypotheses. Thus every `F i (φ M)` is invertible. Joint
conservativity makes `φ M` invertible, also for empty or infinite `I`.
7. Define coevaluation by the inverse of `φ K` applied to the transpose of the left unitor.
Untransposing this equation gives the `K` triangle.
8. For the `D` triangle, contract the two disjoint evaluation pairs in either order.
Tensor interchange and the `K` triangle show that evaluation after the proposed triangle
endomorphism of `D` equals evaluation. Injectivity of transposition makes that endomorphism
`1_D`. These evaluation and coevaluation maps give the reflected dual pair. -/
theorem dualizable_iff_of_jointly_conservative
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] {I : Type w} (D : I → Type u')
    [∀ i, Category.{v'} (D i)] [∀ i, MonoidalCategory (D i)]
    [∀ i, SymmetricCategory (D i)] [∀ i, MonoidalClosed (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hSymmetry : ∀ (i : I) (A B : C),
      Functor.LaxMonoidal.μ (F i) A B ≫ (F i).map (β_ A B).hom =
        (β_ ((F i).obj A) ((F i).obj B)).hom ≫ Functor.LaxMonoidal.μ (F i) B A)
    (hConservative : ∀ {A B : C} (a : A ⟶ B),
      (∀ i : I, IsIso ((F i).map a)) → IsIso a)
    (h : ∀ (i : I) (B : C), ihom B ⋙ F i ≅ F i ⋙ ihom ((F i).obj B))
    (hHomNaturality : ∀ (i : I) {A B : C} (f : A ⟶ B) (T : C),
      (F i).map ((pre f).app T) ≫ (h i A).hom.app T =
        (h i B).hom.app T ≫ (pre ((F i).map f)).app ((F i).obj T))
    (hTranspose : ∀ (i : I) (A B T : C) (g : A ⊗ B ⟶ T),
      curry ((β_ ((F i).obj B) ((F i).obj A)).hom ≫
        Functor.LaxMonoidal.μ (F i) A B ≫ (F i).map g) =
          (F i).map (curry ((β_ B A).hom ≫ g)) ≫ (h i B).hom.app T)
    (K : C) :
    (∃ E : C, Nonempty (ExactPairing K E)) ↔
      ∀ i : I, ∃ E : D i, Nonempty (ExactPairing ((F i).obj K) E) := by
  -- Transpose compatibility already determines the internal-Hom comparison.
  have _ := hHomNaturality
  constructor
  · rintro ⟨E, ⟨p⟩⟩ i
    let := p
    exact ⟨(F i).obj E, ⟨ExactPairing.map (F i) K E⟩⟩
  · intro hK
    have hc (i : I) (B T : C) :
        (Functor.LaxMonoidal.ihomComparison (F i) B).natTrans.app T =
          (h i B).hom.app T := by
      let A := (ihom B).obj T
      have ht := hTranspose i A B T ((β_ A B).hom ≫ (ihom.ev B).app T)
      have hs := hSymmetry i A B
      simp only [Functor.map_comp] at ht
      rw [← Category.assoc (Functor.LaxMonoidal.μ (F i) A B), hs] at ht
      simpa [Functor.LaxMonoidal.ihomComparison_app_eq_curry, Category.assoc,
        ← MonoidalClosed.uncurry_id_eq_ev, A] using ht
    have hi (i : I) : IsIso (Functor.LaxMonoidal.ihomComparison (F i) K).natTrans := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro T
      rw [hc]
      infer_instance
    have hm (i : I) : IsIso ((F i).map (ihomUnitTensorToIhom K K)) := by
      obtain ⟨E, ⟨p⟩⟩ := hK i
      let := p
      let := BraidedCategory.exactPairing_swap ((F i).obj K) E
      let := isIso_ihomUnitTensorToIhom E ((F i).obj K) ((F i).obj K)
      let := hi i
      exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison (F i) K K
    let := hConservative (ihomUnitTensorToIhom K K) hm
    let := exactPairingOfIsIso K
    exact ⟨(ihom K).obj (𝟙_ C), ⟨BraidedCategory.exactPairing_swap _ K⟩⟩

end CategoryTheory
