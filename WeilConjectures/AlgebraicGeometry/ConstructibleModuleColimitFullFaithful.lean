/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitFullFaithfulSurjective
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitFullFaithfulStabilization

/-! # Faithful and fully faithful constructible sheaf descent

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully
faithful paragraphs (blueprint: lem-weil-pbc-constructible-module-colimit-full-faithful).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Faithful and fully faithful constructible sheaf descent along affine limits.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully
faithful paragraphs (blueprint: lem-weil-pbc-constructible-module-colimit-full-faithful).
The proof follows the finite affine presentation, section continuity, and filtered
colimit equality arguments of the node proof.

Proof (node proof, step by step):
1. Replace `I` by the tail `I_{≥ i₀}`; it is nonempty and directed, and the colimit and
   its transition maps are unchanged, so `i₀` may be taken as the initial stage.
2. Choose an affine finite presentation `V → U → F₀ → 0`
   (lem-weil-pbc-constructible-module-finite-presentation): `U`, `V` finite sums of
   lower-shriek free module sheaves on affine étale objects. Its pullbacks to every later
   stage and to `X` are again exact (prop-weil-pbc-inverse-image-modules-exact).
3. Faithfulness: for `h : T → X₀` and a summand `P(W)`, the adjunction `h⁻¹ ⊣ h_*`,
   sheafification and free Yoneda give `Hom(h⁻¹P(W), H) ≅ H(W ×_{X₀} T)`, compatible with
   pullback through the unit section map `ρ` (lem-weil-pbc-free-yoneda-presheaf-module,
   lem-weil-pbc-inverse-image-composition). If `d : F₀ → G₀` pulls back to zero on `X`, the
   finitely many sections of `G₀(U_r)` given by `d` on the summands have zero limit image,
   hence vanish at a common later stage by section continuity
   (lem-weil-pbc-limit-pullback-sections-colimit,
   lem-weil-pbc-filtered-colimit-modules-elementwise); cancel the pulled-back epimorphism.
4. Surjectivity: for `a` on `X`, lift `a ∘ (f₀⁻¹U → f₀⁻¹F₀)` to some `b : U_j → G_j`
   (lem-weil-pbc-affine-free-etale-module-eventual-hom-lift).
5. Relations: `b ∘ r_j` pulls back to zero; by the evaluation bijection of step 3 on the
   affine `V_s` and section continuity based at `X₀`, it vanishes at some `k ≥ j`.
6. Factor `b_k` through the cokernel `F_k` of `r_k` to obtain `a_k`, whose pullback equals
   `a` by cancelling `g_∞`. Injectivity: two representatives with equal limit image are
   moved to a common stage; their difference vanishes later by step 3, using that
   constructibility persists under pullback (prop-constructible-pullback).
7. The evaluation uses the actual adjunction units, so this bijection is the canonical
   comparison. Eventual vanishing and the finite-family clause follow by injectivity,
   surjectivity and a common upper bound of finitely many stages
   (lem-weil-pbc-filtered-colimit-sets-elementwise).
-/
theorem constructibleModuleColimitFullFaithful
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF₀ : Scheme.IsConstructibleEtaleModuleSheaf F₀)
    (hG₀ : Scheme.IsConstructibleEtaleModuleSheaf G₀) :
    ConstructibleModuleColimitCanonicalComparison D c i₀ A F₀ G₀ := by
  unfold ConstructibleModuleColimitCanonicalComparison
  refine ⟨constructibleModuleColimitCanonicalMap_surjective D c hc i₀ A F₀ G₀ hF₀ hG₀,
    constructibleModuleColimitCanonicalMap_stabilizes D c hc i₀ A F₀ G₀ hF₀ hG₀⟩

end AlgebraicGeometry
