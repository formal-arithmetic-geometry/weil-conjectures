module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Relative object descent and representable local finite presentation

Source: Stacks Project, Criteria for Representability, Tag 06CX and
section-limit-preserving (blueprint: lem-sfb-representable-lfp-object-limit-test).

Arrows in a category fibred in groupoids over a base map encode isomorphisms to
pullbacks. This formulation keeps the compatibility square without choosing a cleavage.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A morphism of fibred groupoids representable by algebraic spaces is locally of
finite presentation exactly when objects descend relative to a fixed target object.
No stack condition is imposed on either category.

Source: Stacks Project, Criteria for Representability, Tag 06CX,
lemma-representable-by-spaces-limit-preserving and section-limit-preserving
(blueprint: lem-sfb-representable-lfp-object-limit-test).

The arrow `γ` over the limit projection encodes `p(x) ≅ yᵢ|T`. The arrow `α`
encodes the inverse of the specified isomorphism `xⱼ|T ≅ x`; `β` encodes
`p(xⱼ) ≅ yᵢ|Tⱼ`. Thus `p.map α ≫ β = γ` is exactly the required pullback
compatibility equation, after composing with that inverse.

Proof:
1. Unpack HasSpaceBaseChange: points of the representing space are isomorphism
classes of pairs (x, δ : p(x) ≅ y restricted to the test scheme). Equality of points
supplies an isomorphism of pairs, including its compatibility equation, rather than
merely an isomorphism of underlying objects; use def-trf-algebraic-space.
2. Restrict a directed system to the nonempty directed tail j ≥ i. Its limit is
unchanged, including over Tᵢ: extend a cone to k through any j ≥ i,k. A common
upper bound proves independence and compatibility. No transition hypothesis is needed.
3. If every representing map is locally finitely presented, apply
lem-sfb-space-relative-affine-limit-criterion over Tᵢ to this tail. The target Hom
sets are singletons. Clause (1) of lem-weil-pbc-filtered-colimit-sets-elementwise
supplies a stage point. Step 1 converts its equality at the limit into the required
isomorphism of pairs and hence the displayed equation.
4. Conversely fix a representing space over B. For any directed affine B-system,
its limit is also a limit over S. Choose one index and restrict the fixed object y
there. Relative object descent and step 1 descend every point of the space to a
stage. Apply lem-sfb-space-surjective-affine-limit-criterion with target B, whose
relative Hom sets are singletons, to deduce local finite presentation. -/
theorem representable_lfp_iff_relative_objects_descend
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (p : BasedFunctor F G) (_hF : IsFibredInGroupoids F) (_hG : IsFibredInGroupoids G)
    (_hp : IsRepresentableByAlgebraicSpaces p) :
    ModuliSpaceTest @LocallyOfFinitePresentation p ↔
      ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
        (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
        (∀ i : I, IsAffine (D.obj (op i)).left) → Nonempty (IsLimit c) →
        ∀ (i : I) (yi : Functor.Fiber G.p (D.obj (op i)))
          (x : Functor.Fiber F.p c.pt) (γ : p.obj x.val ⟶ yi.val),
          G.p.IsHomLift (c.π.app (op i)) γ →
          ∃ (j : I) (hij : i ≤ j) (xj : Functor.Fiber F.p (D.obj (op j)))
            (α : x.val ⟶ xj.val) (β : p.obj xj.val ⟶ yi.val),
            F.p.IsHomLift (c.π.app (op j)) α ∧
              G.p.IsHomLift (D.map (homOfLE hij).op) β ∧ p.map α ≫ β = γ := by
  sorry

end CategoryTheory
