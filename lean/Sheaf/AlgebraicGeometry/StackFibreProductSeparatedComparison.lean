/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.AlgebraicStackChangeBaseToIntegers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicModuliStack

/-! # Separated comparison between fibre products of stacks

Source: Stacks Project, Morphisms of Stacks, Tag 050H, and Categories,
lemma-fibre-product-after-map (blueprint: lem-sfb-stack-fibre-product-separated-comparison).

The comparison applies the intermediate functor to the specified isomorphism.
The canonical functor into the diagonal pullback retains that same isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Apply the intermediate functor to the comparison isomorphism of a 2-fibre product.
Source: Stacks, Tag 050H, displayed square
(blueprint: lem-sfb-stack-fibre-product-separated-comparison). -/
def moduliFibreProductComparison {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (a : BasedFunctor F H) (b : BasedFunctor G H) (h : BasedFunctor H D) :
    BasedFunctor (moduliTwoFiberProduct a b) (moduliTwoFiberProduct (a.comp h) (b.comp h))
    where
  obj x := ⟨⟨x.obj.left, x.obj.right, h.map x.obj.hom⟩, by
    have : IsIso x.obj.hom := x.property.1
    have := x.property.2
    exact ⟨inferInstance, inferInstance⟩⟩
  map f := ObjectProperty.homMk
    { left := f.hom.left
      right := f.hom.right
      w := by
        change h.map (a.map f.hom.left) ≫ h.map _ = h.map _ ≫ h.map (b.map f.hom.right)
        rw [← Functor.map_comp, ← Functor.map_comp, f.hom.w] }
  w := rfl

/-- The right-hand map of the diagonal square applies the two given functors.
Source: Stacks, Tag 050H, displayed square
(blueprint: lem-sfb-stack-fibre-product-separated-comparison). -/
def moduliFibreProductPair {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (a : BasedFunctor F H) (b : BasedFunctor G H) (h : BasedFunctor H D) :
    BasedFunctor (moduliTwoFiberProduct (a.comp h) (b.comp h)) (moduliTwoFiberProduct h h)
    where
  obj x := ⟨⟨a.obj x.obj.left, b.obj x.obj.right, x.obj.hom⟩,
    x.property.1, by rw [a.w_obj]; exact x.property.2⟩
  map f := ObjectProperty.homMk
    { left := a.map f.hom.left
      right := b.map f.hom.right
      w := f.hom.w }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact a.map_id _
    · exact b.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact a.map_comp _ _
    · exact b.map_comp _ _
  w := by
    change (ObjectProperty.ι _ ⋙ Comma.fst (a.comp h).toFunctor (b.comp h).toFunctor) ⋙
      a.toFunctor ⋙ H.p = _
    rw [a.w]
    rfl

/-- The canonical comparison into the pullback of the diagonal. The structural arrow
is `(id, φ)` from `(a(x),a(x),id)` to `(a(x),b(y),h(φ))`, so this specifies the
commutativity 2-isomorphism, rather than choosing an unrelated equivalence.
Source: Stacks, Tag 050H, displayed square, and Categories, lemma-fibre-product-after-map
(blueprint: lem-sfb-stack-fibre-product-separated-comparison). -/
def moduliFibreProductDiagonalComparison {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (a : BasedFunctor F H) (b : BasedFunctor G H) (h : BasedFunctor H D) :
    BasedFunctor (moduliTwoFiberProduct a b)
      (moduliTwoFiberProduct (moduliRelativeDiagonal h) (moduliFibreProductPair a b h))
    where
  obj x := by
    have : IsIso x.obj.hom := x.property.1
    let e : (moduliRelativeDiagonal h).obj (a.obj x.obj.left) ≅
        (moduliFibreProductPair a b h).obj ((moduliFibreProductComparison a b h).obj x) :=
      ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) (asIso x.obj.hom) (by
        change h.map (𝟙 _) ≫ h.map x.obj.hom = 𝟙 _ ≫ h.map x.obj.hom
        simp))
    have : H.p.IsHomLift (𝟙 (H.p.obj (a.obj x.obj.left)))
        ((moduliTwoFiberFst h h).map e.hom) := by
      change H.p.IsHomLift (𝟙 (H.p.obj (a.obj x.obj.left))) (𝟙 (a.obj x.obj.left))
      infer_instance
    exact ⟨⟨a.obj x.obj.left, (moduliFibreProductComparison a b h).obj x, e.hom⟩,
      inferInstance, (moduliTwoFiberFst h h).isHomLift_map _ _⟩
  map f := ObjectProperty.homMk
    { left := a.map f.hom.left
      right := (moduliFibreProductComparison a b h).map f
      w := by
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · change a.map f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ a.map f.hom.left
          simp
        · exact f.hom.w }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact a.map_id _
    · exact (moduliFibreProductComparison a b h).map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact a.map_comp _ _
    · exact (moduliFibreProductComparison a b h).map_comp _ _
  w := by
    change (ObjectProperty.ι _ ⋙ Comma.fst a.toFunctor b.toFunctor) ⋙
      a.toFunctor ⋙ H.p = _
    rw [a.w]
    rfl

/-- The relative diagonal square is 2-cartesian; its top comparison is representable
by algebraic spaces and is separated whenever the bottom diagonal is separated.
For a representable map, `ModuliSchemeTest IsClosedImmersion` on its relative diagonal
means that each algebraic-space scheme base change has closed-immersion diagonal.
Source: Stacks, Tag 050H, displayed square and parts (1), (3)
(blueprint: lem-sfb-stack-fibre-product-separated-comparison).

Proof: Apply part (2) of lem-sfb-groupoid-diagonal-two-pullback-identities to `a`, `b`
and the structure map of `H`. The canonical functor sends the structural isomorphism
`φ` to `(id, φ)` and is an equivalence over the base. The DM definition gives the
representability of the bottom diagonal. The base-change stability in
lem-sfb-fibred-groupoid-representable-smooth-calculus gives representability of the top
map. For every scheme `T` mapping to the product, its pullback is canonically equivalent
over `T` to the pullback of the bottom diagonal. The separatedness hypothesis gives a
closed-immersion diagonal for the latter algebraic space; this is precisely the diagonal
of the former under that equivalence. No separation or properness of `S` is used. -/
theorem stack_fibreProduct_separated_comparison {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (H : BasedCategory.{v₃, w₃} (Over S)) (a : BasedFunctor F H) (b : BasedFunctor G H)
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (hH : IsDeligneMumfordModuliStack H) :
    (moduliFibreProductDiagonalComparison a b (moduliBaseStructure H)).toFunctor.IsEquivalence ∧
      IsRepresentableByAlgebraicSpaces
        (moduliFibreProductComparison a b (moduliBaseStructure H)) ∧
      (ModuliSchemeTest @IsClosedImmersion
          (moduliRelativeDiagonal (moduliRelativeDiagonal (moduliBaseStructure H))) →
        ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal
          (moduliFibreProductComparison a b (moduliBaseStructure H)))) :=
  sorry

/-- The same comparison square over `Spec ℤ`, for the underlying stacks.
The separatedness assumption is on the absolute diagonal, independently of the relative
one. `Spec (ULift ℤ)` supplies the integer spectrum in the universe of `S`.
Source: Stacks, Tag 050H, and Algebraic Stacks, Tags 04X5--04X6
(blueprint: lem-sfb-stack-fibre-product-separated-comparison).

Proof: An étale DM atlas is smooth by
lem-sfb-fibred-groupoid-representable-smooth-calculus, so the given DM stacks are
algebraic stacks. Part (1) of lem-sfb-algebraic-stack-change-base-to-integers makes
their underlying stacks algebraic over the integers, preserving the total categories,
morphisms and the fibre product over `H`. Apply the groupoid diagonal square identity
to their structure maps over the integers. Its canonical comparison is an equivalence.
The absolute diagonal is representable, so its base change is representable. Each
scheme test of the top comparison is the same algebraic-space test of the absolute
bottom diagonal. Its diagonal is a closed immersion under the displayed absolute
separatedness hypothesis, proving the last assertion. -/
theorem stack_fibreProduct_separated_comparison_overIntegers {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (H : BasedCategory.{v₃, w₃} (Over S)) (a : BasedFunctor F H) (b : BasedFunctor G H)
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (hH : IsDeligneMumfordModuliStack H) :
    Functor.IsEquivalence (moduliFibreProductDiagonalComparison
      (moduliChangeBaseMap (specULiftZIsTerminal.from S) a)
      (moduliChangeBaseMap (specULiftZIsTerminal.from S) b)
      (moduliBaseStructure (moduliChangeBase (specULiftZIsTerminal.from S) H))).toFunctor ∧
      IsRepresentableByAlgebraicSpaces (moduliFibreProductComparison
        (moduliChangeBaseMap (specULiftZIsTerminal.from S) a)
        (moduliChangeBaseMap (specULiftZIsTerminal.from S) b)
        (moduliBaseStructure (moduliChangeBase (specULiftZIsTerminal.from S) H))) ∧
      (ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal
          (moduliDiagonalOverIntegers H)) →
        ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal
          (moduliFibreProductComparison
            (moduliChangeBaseMap (specULiftZIsTerminal.from S) a)
            (moduliChangeBaseMap (specULiftZIsTerminal.from S) b)
            (moduliBaseStructure (moduliChangeBase (specULiftZIsTerminal.from S) H))))) :=
  sorry

end CategoryTheory
