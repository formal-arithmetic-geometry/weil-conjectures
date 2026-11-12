/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Unbounded complexes with cohomology in a weak Serre class: amplitude and finite window

Let `G : D(C) ⥤ D(D)` be a triangulated functor which does not lower degrees and preserves
countable products, where `C` and `D` have exact countable products. Let `P` be a class of objects
of `C` and `Q` a weak Serre class of objects of `D`. Assume that `G` sends every object of `P`,
placed in degree `0`, into degrees `≤ d` and to a complex with cohomology in `Q`. For a complex
`K` (possibly unbounded) with cohomology in `P`:

* `DerivedCategory.isLE_obj_add_one_of_homologyProperty`: if `K ∈ D^{≤ b}`, then
  `G K ∈ D^{≤ b + d + 1}`, by left completeness;
* `DerivedCategory.isIso_homologyFunctor_map_truncLEι`,
  `DerivedCategory.isIso_homologyFunctor_map_truncGEπ_of_homologyProperty`: the truncation maps
  `K ← τ_{≤ q} K → τ_{≥ q - d - 1} τ_{≤ q} K` induce isomorphisms on `H^q ∘ G`;
* `DerivedCategory.homologyProperty_obj_of_homologyProperty`: `G K` has cohomology in `Q`.

This is the formal part of blueprint `lemma-proper-direct-image-unbounded-complexes`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

section Bounded

variable (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
  [Q.IsClosedUnderKernels] [Q.IsClosedUnderCokernels] [Q.IsClosedUnderExtensions]

omit [P.ContainsZero] in
/-- If a triangulated functor `G` sends the objects of `P`, placed in degree `0`, to complexes
with cohomology in the weak Serre class `Q`, it does so for all bounded complexes with
cohomology in `P` (dévissage along the truncation triangles). -/
lemma homologyProperty_obj_of_bounded
    (hG : ∀ F : C, P F → homologyProperty Q (G.obj ((singleFunctor C 0).obj F)))
    (M : DerivedCategory C) (hM : t.bounded M) (hMP : homologyProperty P M) :
    homologyProperty Q (G.obj M) :=
  prop_of_bounded ((homologyProperty Q).inverseImage G) P hG M hM hMP

end Bounded

variable [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [Abelian.HasKInjectiveResolutions D]
  [HasLimitsOfShape (Discrete ℕ) D] [HasExactLimitsOfShape (Discrete ℕ) D]
  [PreservesLimitsOfShape (Discrete ℕ) G] (d : ℤ)

/-- If `G` sends the objects of `P`, placed in degree `0`, into degrees `≤ d`, it sends every
(possibly unbounded) complex in `D^{≤ b}` with cohomology in `P` into degrees `≤ b + d + 1`:
the bounded truncations `τ_{≥ -n} K` go into degrees `≤ b + d`, and `K` is their homotopy
limit. -/
lemma isLE_obj_add_one_of_homologyProperty
    (hG : ∀ F : C, P F → (G.obj ((singleFunctor C 0).obj F)).IsLE d)
    (K : DerivedCategory C) (hK : homologyProperty P K) (b : ℤ) [K.IsLE b] :
    (G.obj K).IsLE (b + d + 1) := by
  have := isLE_obj_of_forall_isLE_obj_truncGE G K (b + d) fun n ↦
    isLE_obj_of_isLE_of_homologyProperty G d P hG _
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨b, inferInstance⟩⟩ (homologyProperty_truncGE hK _) b
  exact this

omit [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [Abelian.HasKInjectiveResolutions C]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [Abelian.HasKInjectiveResolutions D] [HasLimitsOfShape (Discrete ℕ) D]
  [HasExactLimitsOfShape (Discrete ℕ) D] [PreservesLimitsOfShape (Discrete ℕ) G] in
/-- If `G` does not lower degrees, the map `τ_{≤ q} K ⟶ K` induces an isomorphism on
`H^q ∘ G`. -/
lemma isIso_homologyFunctor_map_truncLEι
    (hG : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (K : DerivedCategory C) (q : ℤ) :
    IsIso ((homologyFunctor D q).map (G.map ((t.truncLEι q).app K))) := by
  have hT := G.map_distinguished _ (t.triangleLEGE_distinguished q (q + 1) rfl K)
  have hB := hG ((t.truncGE (q + 1)).obj K) (q + 1)
    (inferInstanceAs (t.IsGE ((t.truncGE (q + 1)).obj K) (q + 1)))
  exact isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
    (isZero_of_isGE _ (q + 1) _ (by lia) (hX := hB))
    (isZero_of_isGE _ (q + 1) _ (by lia) (hX := hB))

/-- If `G` sends the objects of `P`, placed in degree `0`, into degrees `≤ d`, then for every
complex `K` with cohomology in `P` the map `τ_{≤ q} K ⟶ τ_{≥ q - d - 1} τ_{≤ q} K` induces an
isomorphism on `H^q ∘ G`. -/
lemma isIso_homologyFunctor_map_truncGEπ_of_homologyProperty
    (hG : ∀ F : C, P F → (G.obj ((singleFunctor C 0).obj F)).IsLE d)
    (K : DerivedCategory C) (hK : homologyProperty P K) (q : ℤ) :
    IsIso ((homologyFunctor D q).map
      (G.map ((t.truncGEπ (q - d - 1)).app ((t.truncLE q).obj K)))) := by
  have hT := G.map_distinguished _
    (t.triangleLEGE_distinguished (q - d - 2) (q - d - 1) (by lia) ((t.truncLE q).obj K))
  have hL := isLE_obj_add_one_of_homologyProperty G P d hG
    ((t.truncLE (q - d - 2)).obj ((t.truncLE q).obj K))
    (homologyProperty_truncLE (homologyProperty_truncLE hK q) _) (q - d - 2)
  exact isIso_homologyMap_mor₂ _ hT q (q + 1) rfl
    (isZero_of_isLE _ (q - d - 2 + d + 1) _ (by lia) (hX := hL))
    (isZero_of_isLE _ (q - d - 2 + d + 1) _ (by lia) (hX := hL))

variable (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
  [Q.IsClosedUnderKernels] [Q.IsClosedUnderCokernels] [Q.IsClosedUnderExtensions]

/-- Let `G` not lower degrees and send the objects of `P`, placed in degree `0`, into degrees
`≤ d` and to complexes with cohomology in the weak Serre class `Q`. Then `G` sends every
(possibly unbounded) complex with cohomology in `P` to a complex with cohomology in `Q`: in
degree `q`, `H^q(G K) ≅ H^q(G (τ_{≥ q - d - 1} τ_{≤ q} K))`, and the latter complex is
bounded. -/
lemma homologyProperty_obj_of_homologyProperty
    (hG₁ : ∀ F : C, P F → (G.obj ((singleFunctor C 0).obj F)).IsLE d)
    (hG₂ : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (hG₃ : ∀ F : C, P F → homologyProperty Q (G.obj ((singleFunctor C 0).obj F)))
    (K : DerivedCategory C) (hK : homologyProperty P K) :
    homologyProperty Q (G.obj K) := fun q ↦ by
  have := isIso_homologyFunctor_map_truncLEι G hG₂ K q
  have := isIso_homologyFunctor_map_truncGEπ_of_homologyProperty G P d hG₁ K hK q
  have hW := homologyProperty_obj_of_bounded G P Q hG₃
    ((t.truncGE (q - d - 1)).obj ((t.truncLE q).obj K))
    ⟨⟨q - d - 1, inferInstance⟩, ⟨q, inferInstance⟩⟩
    (homologyProperty_truncGE (homologyProperty_truncLE hK q) _) q
  exact Q.prop_of_iso ((asIso ((homologyFunctor D q).map
    (G.map ((t.truncGEπ (q - d - 1)).app ((t.truncLE q).obj K))))).symm ≪≫
      asIso ((homologyFunctor D q).map (G.map ((t.truncLEι q).app K)))) hW

end DerivedCategory
