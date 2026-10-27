module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Descent of closed immersions of algebraic spaces over affine limits

Source: Stacks Project, Limits of Spaces, Tag 0850, `lemma-descend-closed-immersion`,
in Situation 084W, specialized to affine scheme bases
(blueprint: lem-sfb-space-descend-closed-immersion).

The ambient scheme is Spec Z in universe u. All base changes are Mathlib's actual
pullback functor on presheaves. Representability by closed immersions expresses both
representability and the closed-immersion condition on every scheme test.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type map of qcqs algebraic spaces over an affine stage becomes a
closed immersion at a later stage if its limit base change is a closed immersion.
Source: Stacks Project, Limits of Spaces, Tag 0850, Situation 084W
(blueprint: lem-sfb-space-descend-closed-immersion).

Proof:
1. Choose an affine scheme C₀ with a representable surjective etale map to V₀ by
   [lem-trf-space-qc-finite-affine-atlas-refinement]. Base change to Cᵢ and C.
   The limit base is affine by [lem-weil-pbc-limit-affine-transition]. All these
   charts are affine by [lem-weil-pbc-morphism-affine-schemes-affine] and
   [lem-weil-pbc-affine-morphism-permanence]. Their atlas maps remain surjective
   etale by [lem-trf-space-fibre-products-etale-covers].
2. Put W₀ = U₀ times_V₀ C₀ and Wᵢ = W₀ times_Tᵢ₀ Tᵢ. They are qcqs by
   [lem-weil-pbc-affine-scheme-qcqs] and [lem-sfb-space-qcqs-source-products].
   Their transitions are affine by [lem-sfb-space-affine-locality]. The cofinal
   directed tail above i₀ has limits W and C, by the base-change clause of
   [lem-sfb-space-affine-limits-schematic-stages]: on test sections the two sides
   are the same compatible tuples, using fibre-product associativity.
3. The assumed closed immersion makes W to C a scheme closed immersion. Since C
   is affine, W is affine by [def-weil-closed-immersion]. The eventual-affineness
   clause of [lem-sfb-space-affine-limits-schematic-stages] gives an affine Wₖ,
   and all later Wᵢ are affine.
4. The map Wₖ to Cₖ is locally of finite type by base-change stability and scheme
   compatibility in [lem-sfb-stack-finite-type-calculus]. Both are affine, hence
   qcqs by [lem-weil-pbc-affine-scheme-qcqs]. Apply
   [lem-weil-pbc-descend-closed-immersion] over the tail above k. The limit map is
   W to C and is a closed immersion; thus Wⱼ to Cⱼ is a closed immersion for
   some j above k.
5. The map Wⱼ to Cⱼ is affine by [lem-weil-pbc-morphism-affine-schemes-affine].
   Descent through the surjective etale atlas Cⱼ to Vⱼ, using
   [lem-sfb-space-affine-locality], makes hⱼ affine and representable. Apply
   [lem-trf-space-closed-immersion-cover-descent] with the singleton atlas and
   identity base map. All further scheme tests of Wⱼ to Cⱼ remain closed
   immersions by [lem-weil-pbc-closed-immersion-base-change]. This gives the
   required closed immersion hⱼ, with j above i₀. -/
theorem exists_isClosedImmersion_affine_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (htransition : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (U₀ V₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (h₀ : U₀ ⟶ V₀)
    (v₀ : V₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀)))
    (hUqc : IsQuasiCompact U₀.obj) (hUqs : IsAbsolutelyQuasiSeparated U₀)
    (hVqc : IsQuasiCompact V₀.obj) (hVqs : IsAbsolutelyQuasiSeparated V₀)
    (hlft : MapIsLocally (@LocallyOfFiniteType) h₀)
    (hclosed : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (((Over.pullback (yoneda.map (c.π.app (op i₀)))).map
        (Over.homMk (U := Over.mk (h₀.hom.hom ≫ v₀))
          (V := Over.mk v₀) h₀.hom.hom rfl)).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (((Over.pullback (yoneda.map (D.map (homOfLE hi).op))).map
          (Over.homMk (U := Over.mk (h₀.hom.hom ≫ v₀))
            (V := Over.mk v₀) h₀.hom.hom rfl)).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
