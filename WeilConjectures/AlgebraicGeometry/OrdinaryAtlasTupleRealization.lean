/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEtaleIdentification
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Ordinary atlas modules as compatible section tuples

Source: Stacks Project, Sites, Tag 04TR; Descent, Tags 03DU, 03LC and 05VG.
(blueprint: lem-trf-ordinary-atlas-tuple-realization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Compatible ordinary invertible modules admit a module-sheaf realization on the
small étale site, without a covering assumption or an assertion of local freeness.
The identifications retain the given transitions, including self-overlaps.

Source: Stacks Project, Sites, Tag 04TR (lemma-glue-sheaves), compatible tuples and
local graph evaluation; Descent, Tags 03DU, 03LC and 05VG, tensor-section comparison
(blueprint: lem-trf-ordinary-atlas-tuple-realization).

Proof:
1. Associate to each ordinary module its tensor-section module on the localized
   small étale site of its chart. Invertibility implies quasi-coherence, so étale
   descent makes these section presheaves sheaves. The scheme comparison and its
   unit-normalized composition maps transport α to overlap isomorphisms; their
   diagonal and cocycle identities follow from hdiag and hcocycle.
2. Represent the products of each test object with the charts by the representable
   diagonal. Take compatible tuples of local sections, with the two restrictions
   compared by α. Products indexed by I and I × I have u-small section sets,
   since I : Type u and every local section set is u-small. Define zero, addition,
   negation, scalar multiplication and restriction coordinatewise. The tuple
   equations are preserved by linearity and semilinearity. Limits of sheaves are
   computed sectionwise, so these literal tuples form a module sheaf N in F.Modules.
   This is the construction of lem-trf-space-etale-module-tuple-sheaf, at the
   section universe required here; no choice from an arbitrary existence theorem
   defines its data.
3. On an object mapping to chart i, evaluate the i-coordinate along its graph.
   Its inverse sends y to the tuple whose k-coordinate is α_ki applied to the
   restriction of y. The cocycle proves tuple compatibility; the diagonal law
   proves evaluation after this inverse is the identity. Restricting the (k,i)
   tuple equation to the graph proves the reverse identity. These formulas are
   linear and natural by functoriality of tensor sections. They give e.
4. Pull the (i,j) tuple equation back along the two graph maps from a common
   test object. The unit-normalized pullback comparisons give exactly the stated
   atlasTransitionOver equation. This works also when i = j with distinct lifts.
   No joint surjectivity is used; for the empty family the tuple module is zero. -/
theorem exists_ordinary_atlas_tuple_realization
    {S : Scheme.{u}} (F : AlgebraicSpace S) {I : Type u} (V : I → F.EtaleSite)
    (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ (V i).obj.left)
    (p₂ : ∀ i j : I, R i j ⟶ (V j).obj.left)
    (hR : ∀ i j : I, IsPullback (yoneda.map (p₁ i j)) (yoneda.map (p₂ i j))
      (V i).obj.hom (V j).obj.hom)
    (M : ∀ i : I, (F.etaleForget.obj (V i)).Modules)
    (hM : ∀ i : I, Scheme.Modules.IsInvertible (M i))
    (α : ∀ i j : I,
    (tensorPullback (p₂ i j).left).obj (M j) ≅ (tensorPullback (p₁ i j).left).obj (M i))
    (hdiag : ∀ (i : I) (d : (V i).obj.left ⟶ R i i)
    (h₁ : d ≫ p₁ i i = 𝟙 (V i).obj.left) (h₂ : d ≫ p₂ i i = 𝟙 (V i).obj.left),
    atlasTransitionOver (M i) (M i) (p₁ i i) (p₂ i i) (α i i)
      d (𝟙 (V i).obj.left) (𝟙 (V i).obj.left) h₁ h₂ =
      Iso.refl ((tensorPullback (𝟙 (V i).obj.left.left)).obj (M i)))
    (hcocycle : ∀ (i j k : I) (T : Over S)
    (a : T ⟶ (V i).obj.left) (b : T ⟶ (V j).obj.left) (c : T ⟶ (V k).obj.left)
    (rᵢⱼ : T ⟶ R i j) (rⱼₖ : T ⟶ R j k) (rᵢₖ : T ⟶ R i k)
    (hᵢⱼ₁ : rᵢⱼ ≫ p₁ i j = a) (hᵢⱼ₂ : rᵢⱼ ≫ p₂ i j = b)
    (hⱼₖ₁ : rⱼₖ ≫ p₁ j k = b) (hⱼₖ₂ : rⱼₖ ≫ p₂ j k = c)
    (hᵢₖ₁ : rᵢₖ ≫ p₁ i k = a) (hᵢₖ₂ : rᵢₖ ≫ p₂ i k = c),
    atlasTransitionOver (M i) (M k) (p₁ i k) (p₂ i k) (α i k)
      rᵢₖ a c hᵢₖ₁ hᵢₖ₂ =
    atlasTransitionOver (M j) (M k) (p₁ j k) (p₂ j k) (α j k)
      rⱼₖ b c hⱼₖ₁ hⱼₖ₂ ≪≫
    atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (α i j)
      rᵢⱼ a b hᵢⱼ₁ hᵢⱼ₂) :
    ∃ (N : F.Modules),
    ∃ (e : ∀ i : I, OrdinaryEtaleIdentification F (V i) N (M i)),
        ∀ (i j : I) (T : F.EtaleSite) (a : T ⟶ V i) (b : T ⟶ V j)
          (r : T.obj.left ⟶ R i j)
          (h₁ : r ≫ p₁ i j = a.hom.left) (h₂ : r ≫ p₂ i j = b.hom.left)
          (s : ((tensorPullback (F.etaleForget.map b)).obj (M j)).val.obj (op ⊤)),
          (e i).app T a
            (((atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (α i j)
              r a.hom.left b.hom.left h₁ h₂).hom.app ⊤) s) = (e j).app T b s := by sorry

end AlgebraicGeometry.AlgebraicSpace
