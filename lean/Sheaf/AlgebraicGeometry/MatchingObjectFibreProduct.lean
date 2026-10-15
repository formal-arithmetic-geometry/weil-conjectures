/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.CategoryTheory.ProperFaceMatchingObject

/-!
# Matching schemes of termwise fibre products

Source: Stacks Project, Simplicial Methods, Lemma 018D (lemma-cosk-fibre-product),
and Hypercoverings, Lemma 01GH (lemma-funny-gamma).
(blueprint: lem-weil-pbc-matching-object-fibre-product)

Augmented simplicial schemes are simplicial objects in `Over X`. Products in `Over X`
are fibre products of schemes over `X`. Arbitrary limiting cones specify matching schemes,
including in degree zero, where the proper-face category is empty.
-/

@[expose] public section

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
  let cU : Cone (properFaceDiagram U n) :=
    { pt := MW.pt
      π :=
        { app := fun a ↦ MW.π.app a ≫ p.app (op a.unop.obj.left)
          naturality := by
            intro i j f
            dsimp [properFaceDiagram]
            simp only [Category.id_comp, Category.assoc]
            rw [← p.naturality]
            have hMW : MW.π.app i ≫ W.map (Over.Hom.left f.unop.hom).op =
                MW.π.app j := by
              simpa [properFaceDiagram] using (MW.π.naturality f).symm
            rw [← Category.assoc, hMW] } }
  let cV : Cone (properFaceDiagram V n) :=
    { pt := MW.pt
      π :=
        { app := fun a ↦ MW.π.app a ≫ q.app (op a.unop.obj.left)
          naturality := by
            intro i j f
            dsimp [properFaceDiagram]
            simp only [Category.id_comp, Category.assoc]
            rw [← q.naturality]
            have hMW : MW.π.app i ≫ W.map (Over.Hom.left f.unop.hom).op =
                MW.π.app j := by
              simpa [properFaceDiagram] using (MW.π.naturality f).symm
            rw [← Category.assoc, hMW] } }
  let Mp : MW.pt ⟶ MU.pt := _hMU.lift cU
  let Mq : MW.pt ⟶ MV.pt := _hMV.lift cV
  have hMp (a : ProperFaceCategory n) :
      Mp ≫ MU.π.app (op a) = MW.π.app (op a) ≫ p.app (op a.obj.left) := by
    exact _hMU.fac cU (op a)
  have hMq (a : ProperFaceCategory n) :
      Mq ≫ MV.π.app (op a) = MW.π.app (op a) ≫ q.app (op a.obj.left) := by
    exact _hMV.fac cV (op a)
  have hIso : IsIso (prod.lift Mp Mq) := by
    let r (a : (ProperFaceCategory n)ᵒᵖ) : MU.pt ⨯ MV.pt ⟶
        W.obj (op a.unop.obj.left) :=
      BinaryFan.IsLimit.lift (_hW (op a.unop.obj.left))
        (prod.fst ≫ MU.π.app a) (prod.snd ≫ MV.π.app a)
    have hrp (a : (ProperFaceCategory n)ᵒᵖ) :
        r a ≫ p.app (op a.unop.obj.left) = prod.fst ≫ MU.π.app a :=
      BinaryFan.IsLimit.lift_fst (_hW _) _ _
    have hrq (a : (ProperFaceCategory n)ᵒᵖ) :
        r a ≫ q.app (op a.unop.obj.left) = prod.snd ≫ MV.π.app a :=
      BinaryFan.IsLimit.lift_snd (_hW _) _ _
    let c : Cone (properFaceDiagram W n) :=
      { pt := MU.pt ⨯ MV.pt
        π :=
          { app := r
            naturality := by
              intro i j f
              dsimp [properFaceDiagram]
              rw [Category.id_comp]
              symm
              apply BinaryFan.IsLimit.hom_ext (_hW (op j.unop.obj.left))
              · change (r i ≫ W.map (Over.Hom.left f.unop.hom).op) ≫
                  p.app (op j.unop.obj.left) = r j ≫ p.app (op j.unop.obj.left)
                rw [Category.assoc, p.naturality, ← Category.assoc, hrp, hrp, Category.assoc]
                exact congrArg (fun k ↦ prod.fst ≫ k) (MU.π.naturality f).symm
              · change (r i ≫ W.map (Over.Hom.left f.unop.hom).op) ≫
                  q.app (op j.unop.obj.left) = r j ≫ q.app (op j.unop.obj.left)
                rw [Category.assoc, q.naturality, ← Category.assoc, hrq, hrq, Category.assoc]
                exact congrArg (fun k ↦ prod.snd ≫ k) (MV.π.naturality f).symm } }
    let inv : MU.pt ⨯ MV.pt ⟶ MW.pt := _hMW.lift c
    have hinv (a : (ProperFaceCategory n)ᵒᵖ) : inv ≫ MW.π.app a = r a :=
      _hMW.fac c a
    refine ⟨⟨inv, ?_, ?_⟩⟩
    · apply _hMW.hom_ext
      intro a
      rw [Category.assoc, hinv]
      apply BinaryFan.IsLimit.hom_ext (_hW (op a.unop.obj.left))
      · change (prod.lift Mp Mq ≫ r a) ≫ p.app (op a.unop.obj.left) =
          (𝟙 MW.pt ≫ MW.π.app a) ≫ p.app (op a.unop.obj.left)
        rw [Category.assoc, hrp, ← Category.assoc, prod.lift_fst, Category.id_comp]
        exact hMp a.unop
      · change (prod.lift Mp Mq ≫ r a) ≫ q.app (op a.unop.obj.left) =
          (𝟙 MW.pt ≫ MW.π.app a) ≫ q.app (op a.unop.obj.left)
        rw [Category.assoc, hrq, ← Category.assoc, prod.lift_snd, Category.id_comp]
        exact hMq a.unop
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
        apply _hMU.hom_ext
        intro a
        rw [Category.assoc, hMp a.unop, ← Category.assoc, hinv, hrp]
        rfl
      · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
        apply _hMV.hom_ext
        intro a
        rw [Category.assoc, hMq a.unop, ← Category.assoc, hinv, hrq]
        rfl
  refine ⟨Mp, Mq, hMp, hMq, hIso, ?_⟩
  apply BinaryFan.IsLimit.hom_ext (prodIsProd MU.pt MV.pt)
  · change μW ≫ prod.lift Mp Mq ≫ prod.fst =
      prod.lift (p.app (op (SimplexCategory.mk n)) ≫ μU)
        (q.app (op (SimplexCategory.mk n)) ≫ μV) ≫ prod.fst
    simp only [prod.lift_fst]
    apply _hMU.hom_ext
    intro a
    rw [Category.assoc, Category.assoc, hMp a.unop, ← Category.assoc, _hμW a.unop]
    rw [_hμU a.unop]
    exact p.naturality a.unop.obj.hom.op
  · change μW ≫ prod.lift Mp Mq ≫ prod.snd =
      prod.lift (p.app (op (SimplexCategory.mk n)) ≫ μU)
        (q.app (op (SimplexCategory.mk n)) ≫ μV) ≫ prod.snd
    simp only [prod.lift_snd]
    apply _hMV.hom_ext
    intro a
    rw [Category.assoc, Category.assoc, hMq a.unop, ← Category.assoc, _hμW a.unop]
    rw [_hμV a.unop]
    exact q.naturality a.unop.obj.hom.op

end AlgebraicGeometry
