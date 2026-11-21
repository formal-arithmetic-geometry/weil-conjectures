/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionMap

/-!
# Trace counits tensored with a fixed object

Let `π_{K, L} : R K ⊗ L ⟶ R (K ⊗ P L)` be a projection map satisfying the associativity law for
a comparison `δ : P (L ⊗ L') ⟶ P L ⊗ P L'`, let `T` be an object with `π_{T, -}` invertible and
`t : R T ⟶ 𝟙`. The *trace counit* `R (T ⊗ P K) ⟶ K` is the inverse of the projection map
followed by `t ▷ K` and the left unitor. For `a : P N_Y ⟶ N_X`, tensoring the trace counit with
`N_Y` is the trace counit at `K ⊗ N_Y`, read through the comparison `c_M = π_{M, N_Y} ≫ R (M ◁ a)`
of `R` with `- ⊗ N` and the associator (`CategoryTheory.Adjunction.traceCounit_whiskerRight`,
`CategoryTheory.Adjunction.traceCounit_whiskerRight_of_iso`). This is the formal input for the
compatibility of the counit of the projective-line adjunction with change of finite coefficients.

## Implementation notes

`CategoryTheory.Adjunction.traceCounit_curriedTensor` restates the result with the curried tensor
products `curriedTensor`, with an object `K_N` equal to `K ⊗ N_Y`, and with the inverses of the
projection maps, the trace counits and the associator given by morphisms equal to them. For the
derived categories of étale sheaves, whose tensor products are given as functors, applying it
then only asks the kernel to compare objects, and never projection maps evaluated at objects
written differently, which it cannot do in reasonable time.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory

variable {CX CY : Type*} [Category* CX] [Category* CY] [MonoidalCategory CX]
  [MonoidalCategory CY] {R : CX ⥤ CY} {P : CY ⥤ CX}
  {δ : ∀ L L', P.obj (L ⊗ L') ⟶ P.obj L ⊗ P.obj L'}
  (π : ∀ K L, R.obj K ⊗ L ⟶ R.obj (K ⊗ P.obj L))
  (hπ : ∀ K L L', π K L ▷ L' ≫ π (K ⊗ P.obj L) L' ≫ R.map (α_ K (P.obj L) (P.obj L')).hom =
    (α_ (R.obj K) L L').hom ≫ π K (L ⊗ L') ≫ R.map (K ◁ δ L L'))
  {NY : CY} {NX : CX} (a : P.obj NY ⟶ NX)

include hπ in
/-- **The inverse of a projection map tensored with a fixed object.** With the notation of
`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`, let `e : P (K ⊗ N_Y) ≅ P K ⊗ N_X` be
the isomorphism `δ ≫ P K ◁ a`, and let `π_{T, K}` be the morphism of an isomorphism `p`. Then the
comparison `c_{T ⊗ P K}` followed by `R (α)` and `R (T ◁ e⁻¹)` is
`p⁻¹ ▷ N_Y ≫ α ≫ π_{T, K ⊗ N_Y}`. -/
lemma comp_map_whiskerLeft_inv_eq (T : CX) (K : CY) (e : P.obj (K ⊗ NY) ≅ P.obj K ⊗ NX)
    (he : e.hom = δ K NY ≫ P.obj K ◁ a) (p : R.obj T ⊗ K ≅ R.obj (T ⊗ P.obj K))
    (hp : p.hom = π T K) :
    π (T ⊗ P.obj K) NY ≫ R.map ((T ⊗ P.obj K) ◁ a) ≫ R.map (α_ T (P.obj K) NX).hom ≫
        R.map (T ◁ e.inv) =
      p.inv ▷ NY ≫ (α_ (R.obj T) K NY).hom ≫ π T (K ⊗ NY) := by
  have h := projectionMap_whiskerRight_comp π hπ a T K
  rw [← he, ← hp] at h
  rw [← cancel_epi (p.hom ▷ NY), reassoc_of% h, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, id_comp]
  simp only [← R.map_comp, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, R.map_id, comp_id]

include hπ in
/-- **Trace counits tensored with a fixed object.** With the notation of
`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`, let `t : R T ⟶ 𝟙`, let `π_{T, K}`
and `π_{T, K ⊗ N_Y}` be the morphisms of isomorphisms `p` and `p'`, and let
`e : P (K ⊗ N_Y) ≅ P K ⊗ N_X` be `δ ≫ P K ◁ a`. Then the trace counit `p⁻¹ ≫ t ▷ K ≫ λ_K`,
tensored with `N_Y`, is the comparison `c_{T ⊗ P K}` followed by `R (α ≫ T ◁ e⁻¹)` and the trace
counit `p'⁻¹ ≫ t ▷ (K ⊗ N_Y) ≫ λ_{K ⊗ N_Y}`. -/
lemma traceCounit_whiskerRight (T : CX) (t : R.obj T ⟶ 𝟙_ CY) (K : CY)
    (e : P.obj (K ⊗ NY) ≅ P.obj K ⊗ NX) (he : e.hom = δ K NY ≫ P.obj K ◁ a)
    (p : R.obj T ⊗ K ≅ R.obj (T ⊗ P.obj K)) (hp : p.hom = π T K)
    (p' : R.obj T ⊗ (K ⊗ NY) ≅ R.obj (T ⊗ P.obj (K ⊗ NY))) (hp' : p'.hom = π T (K ⊗ NY)) :
    π (T ⊗ P.obj K) NY ≫ R.map ((T ⊗ P.obj K) ◁ a) ≫ R.map (α_ T (P.obj K) NX).hom ≫
        R.map (T ◁ e.inv) ≫ p'.inv ≫ t ▷ (K ⊗ NY) ≫ (λ_ (K ⊗ NY)).hom =
      (p.inv ≫ t ▷ K ≫ (λ_ K).hom) ▷ NY := by
  rw [reassoc_of% (comp_map_whiskerLeft_inv_eq π hπ a T K e he p hp), ← hp',
    Iso.hom_inv_id_assoc, ← associator_naturality_left_assoc, leftUnitor_tensor_hom,
    Iso.hom_inv_id_assoc]
  simp only [comp_whiskerRight]

include hπ in
/-- **The full trace counit tensored with a fixed object.** With the notation of
`CategoryTheory.Adjunction.traceCounit_whiskerRight`, let `G` be a functor with identifications
`γ_K : G K ≅ T ⊗ P K` and `γ_{K ⊗ N_Y}`, and let `θ : G K ⊗ N_X ⟶ G (K ⊗ N_Y)` be compatible
with them through the associator and `e⁻¹`. If `π` is natural in its first variable, then the
trace counit `R γ_K ≫ p⁻¹ ≫ t ▷ K ≫ λ_K`, tensored with `N_Y`, is the comparison `c_{G K}`
followed by `R θ` and the trace counit `R γ_{K ⊗ N_Y} ≫ p'⁻¹ ≫ t ▷ (K ⊗ N_Y) ≫ λ_{K ⊗ N_Y}`. -/
lemma traceCounit_whiskerRight_of_iso
    (hnat : ∀ {K K'} (φ : K ⟶ K') L, R.map φ ▷ L ≫ π K' L = π K L ≫ R.map (φ ▷ P.obj L))
    (T : CX) (t : R.obj T ⟶ 𝟙_ CY) {G : CY ⥤ CX} (K : CY)
    (γK : G.obj K ≅ T ⊗ P.obj K) (γKN : G.obj (K ⊗ NY) ≅ T ⊗ P.obj (K ⊗ NY))
    (e : P.obj (K ⊗ NY) ≅ P.obj K ⊗ NX) (he : e.hom = δ K NY ≫ P.obj K ◁ a)
    (p : R.obj T ⊗ K ≅ R.obj (T ⊗ P.obj K)) (hp : p.hom = π T K)
    (p' : R.obj T ⊗ (K ⊗ NY) ≅ R.obj (T ⊗ P.obj (K ⊗ NY))) (hp' : p'.hom = π T (K ⊗ NY))
    (θ : G.obj K ⊗ NX ⟶ G.obj (K ⊗ NY))
    (hθ : θ ≫ γKN.hom = γK.hom ▷ NX ≫ (α_ T (P.obj K) NX).hom ≫ T ◁ e.inv) :
    (π (G.obj K) NY ≫ R.map (G.obj K ◁ a)) ≫ R.map θ ≫
        (R.map γKN.hom ≫ p'.inv ≫ t ▷ (K ⊗ NY) ≫ (λ_ (K ⊗ NY)).hom) =
      (R.map γK.hom ≫ p.inv ≫ t ▷ K ≫ (λ_ K).hom) ▷ NY := by
  rw [comp_whiskerRight, ← traceCounit_whiskerRight π hπ a T t K e he p hp p' hp',
    reassoc_of% (hnat _ _)]
  simp only [assoc]
  congr 1
  simp only [← R.map_comp_assoc]
  rw [hθ, whisker_exchange_assoc]

include hπ in
/-- **Trace counits tensored with a fixed object, curried form.** The statement of
`CategoryTheory.Adjunction.traceCounit_whiskerRight_of_iso`, written with the curried tensor
products `curriedTensor`, with an object `K_N` equal to `K ⊗ N_Y` in place of `K ⊗ N_Y`, and with
the inverses of the projection maps, the trace counits, the associator and the tensor comparison
given by morphisms equal to them. This is the form in which it applies to categories whose tensor
products are given as functors, such as derived categories. -/
lemma traceCounit_curriedTensor
    (hnat : ∀ {K K'} (φ : K ⟶ K') L, R.map φ ▷ L ≫ π K' L = π K L ≫ R.map (φ ▷ P.obj L))
    (T : CX) (t : R.obj T ⟶ 𝟙_ CY) {G : CY ⥤ CX} (K KN : CY) (hKN : K ⊗ NY = KN)
    (ρ : ((curriedTensor CY).flip.obj NY).obj K ⟶ KN) (hρ : ρ = eqToHom hKN)
    (γK : G.obj K ≅ ((curriedTensor CX).obj T).obj (P.obj K))
    (γKN : G.obj KN ≅ ((curriedTensor CX).obj T).obj (P.obj KN))
    (δKN : P.obj KN ⟶ P.obj K ⊗ P.obj NY) (hδ : HEq δKN (δ K NY))
    (e : P.obj KN ≅ ((curriedTensor CX).flip.obj NX).obj (P.obj K))
    (he : e.hom = δKN ≫ P.obj K ◁ a)
    (αT : ((curriedTensor CX).flip.obj NX).obj (((curriedTensor CX).obj T).obj (P.obj K)) ≅
      ((curriedTensor CX).obj T).obj (((curriedTensor CX).flip.obj NX).obj (P.obj K)))
    (hαT : αT.hom = (α_ T (P.obj K) NX).hom)
    (pinv : R.obj (((curriedTensor CX).obj T).obj (P.obj K)) ⟶
      ((curriedTensor CY).obj (R.obj T)).obj K)
    (hp₁ : π T K ≫ pinv = 𝟙 _) (hp₂ : pinv ≫ π T K = 𝟙 _)
    (pinv' : R.obj (((curriedTensor CX).obj T).obj (P.obj KN)) ⟶
      ((curriedTensor CY).obj (R.obj T)).obj KN)
    (hp₁' : π T KN ≫ pinv' = 𝟙 _) (hp₂' : pinv' ≫ π T KN = 𝟙 _)
    (τK : ((curriedTensor CY).obj (R.obj T)).obj K ⟶ K) (hτK : τK = t ▷ K ≫ (λ_ K).hom)
    (τKN : ((curriedTensor CY).obj (R.obj T)).obj KN ⟶ KN) (hτKN : τKN = t ▷ KN ≫ (λ_ KN).hom)
    (θ : ((curriedTensor CX).flip.obj NX).obj (G.obj K) ⟶ G.obj KN)
    (hθ : θ ≫ γKN.hom = ((curriedTensor CX).flip.obj NX).map γK.hom ≫ αT.hom ≫
      ((curriedTensor CX).obj T).map e.inv) :
    (π (G.obj K) NY ≫ R.map (((curriedTensor CX).obj (G.obj K)).map a)) ≫ R.map θ ≫
        (R.map γKN.hom ≫ pinv' ≫ τKN) =
      ((curriedTensor CY).flip.obj NY).map (R.map γK.hom ≫ pinv ≫ τK) ≫ ρ := by
  subst hKN hρ hτK hτKN
  rw [eqToHom_refl]
  erw [comp_id]
  rw [hαT] at hθ
  rw [eq_of_heq hδ] at he
  exact traceCounit_whiskerRight_of_iso π hπ a hnat T t K γK γKN e he ⟨π T K, pinv, hp₁, hp₂⟩ rfl
    ⟨π T (K ⊗ NY), pinv', hp₁', hp₂'⟩ rfl θ hθ

end CategoryTheory.Adjunction
