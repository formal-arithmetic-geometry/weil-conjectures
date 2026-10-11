/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.CategoryTheory.ProperFaceMatchingObject

/-!
# Matching schemes of termwise fibre products

Source: Stacks Project, Simplicial Methods, Lemma 018D (lemma-cosk-fibre-product),
and Hypercoverings, Lemma 01GH (lemma-funny-gamma).
(blueprint: lem-weil-pbc-matching-object-fibre-product)

Augmented simplicial schemes are simplicial objects in `Over X`. Products in `Over X`
are fibre products of schemes over `X`. Arbitrary limiting cones specify matching schemes,
including in degree zero, where the proper-face category is empty.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject

namespace AlgebraicGeometry

/-- Matching schemes commute with termwise fibre products, compatibly with matching maps.
Source: Stacks Project, Simplicial Methods, Lemma 018D; Hypercoverings, Lemma 01GH.
(blueprint: lem-weil-pbc-matching-object-fibre-product)

Proof:
1. In degree zero the boundary category is empty. Each matching scheme is terminal over
   `X`, hence is `X` up to its unique isomorphism; `X ×_X X` is again terminal. The
   matching-map assertion is the assertion that its two projections are the augmentations.
2. In positive degree, a cone from a test scheme `T` over `X` to the proper-face diagram
   of `W` is exactly a pair of cones to the diagrams of `U` and `V`: project each component
   along `p` and `q`. Conversely use the termwise fibre-product universal property to
   combine each pair of components. The compatibility equations follow after both
   projections, and uniqueness in the fibre product gives the equations themselves.
3. These constructions are inverse and natural in `T`. The matching-cone universal
   properties therefore give inverse morphisms between `M_n(W)` and the fibre product of
   `M_n(U)` and `M_n(V)`. Their projected components characterize the induced maps
   `M_n(p)` and `M_n(q)` uniquely (def-pc-fibre-product and the matching universal property
   of def-weil-pbc-finite-split-hypercover).
4. The components of the matching map of `W` are its simplicial operators. Naturality of
   `p` and `q` identifies their projections with the components of the two matching maps
   composed with the degree-n projections. Limit uniqueness and product uniqueness give
   the displayed matching-map equation, including in degree zero. -/
theorem matching_object_fibre_product
    (X : Scheme.{u}) (U V W : SimplicialObject (Over X))
    (p : W ⟶ U) (q : W ⟶ V)
    (_hW : ∀ Δ : SimplexCategoryᵒᵖ, IsLimit (BinaryFan.mk (p.app Δ) (q.app Δ)))
    (n : ℕ)
    (MU : Cone (properFaceDiagram U n)) (MV : Cone (properFaceDiagram V n))
    (MW : Cone (properFaceDiagram W n))
    (_hMU : IsLimit MU) (_hMV : IsLimit MV) (_hMW : IsLimit MW)
    (μU : U.obj (op (SimplexCategory.mk n)) ⟶ MU.pt)
    (μV : V.obj (op (SimplexCategory.mk n)) ⟶ MV.pt)
    (μW : W.obj (op (SimplexCategory.mk n)) ⟶ MW.pt)
    (_hμU : ∀ a : ProperFaceCategory n, μU ≫ MU.π.app (op a) = U.map a.obj.hom.op)
    (_hμV : ∀ a : ProperFaceCategory n, μV ≫ MV.π.app (op a) = V.map a.obj.hom.op)
    (_hμW : ∀ a : ProperFaceCategory n, μW ≫ MW.π.app (op a) = W.map a.obj.hom.op) :
    ∃ (Mp : MW.pt ⟶ MU.pt) (Mq : MW.pt ⟶ MV.pt),
      (∀ a : ProperFaceCategory n,
        Mp ≫ MU.π.app (op a) = MW.π.app (op a) ≫ p.app (op a.obj.left)) ∧
      (∀ a : ProperFaceCategory n,
        Mq ≫ MV.π.app (op a) = MW.π.app (op a) ≫ q.app (op a.obj.left)) ∧
      IsIso (prod.lift Mp Mq) ∧
      μW ≫ prod.lift Mp Mq =
        prod.lift (p.app (op (SimplexCategory.mk n)) ≫ μU)
          (q.app (op (SimplexCategory.mk n)) ≫ μV) := by
  sorry

end AlgebraicGeometry
