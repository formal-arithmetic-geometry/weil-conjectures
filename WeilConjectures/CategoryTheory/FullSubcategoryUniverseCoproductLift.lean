/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Coproduct inheritance across indexing universes

Source: blueprint main-20261015, `det-proper-image-localizing-open`, Formal properties and
Localizing categories; Stacks Tags 002F, 05QM, 05QX, 014V
(blueprint: lem-sf-full-subcategory-universe-coproduct-lift).

The larger indexing universe is `max w w'`. No ambient large coproduct existence is assumed.
The first statement applies separately to each of the two object properties in the node.
-/

@[expose] public section

set_option autoImplicit false

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

/-- Closure under existing large coproducts transfers to smaller indices with the very same
coprojections, and gives creation, preservation, reflection and existence in the full subcategory.
Source: blueprint `det-proper-image-localizing-open`, Localizing categories; Stacks Tag 002F
(blueprint: lem-sf-full-subcategory-universe-coproduct-lift).

Proof:
1. Reindex any coproduct cocone along `ULift.down`, inverse to `ULift.up`. Given a family of
legs on either indexing type, compose with the inverse bijection. The ambient universal
property gives the unique mediating arrow, and the two inverse equations verify its
factorizations and uniqueness. This includes the empty family and retains each actual leg.
Apply large-index closure to this particular existing reindexed coproduct to obtain small
closure; no existence of all large coproducts is used.
2. For a diagram in the full subcategory, its ambient coproduct vertex has the property by
step 1. Equip this same vertex with that proof and use the same coprojections. Fullness
restricts the ambient mediating arrows and their uniqueness, so the inclusion creates the
coproduct and reflects colimit cocones.
3. Compare any subcategory colimit cocone with the inherited one. Their unique comparison
arrows are inverse. Transporting the ambient universal property across this isomorphism
proves preservation for every subcategory colimit cocone. If all ambient small coproducts
exist, apply the construction to every diagram. Repeat this argument for the target property.
-/
theorem fullSubcategory_universe_coproduct_inheritance
    {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (J : Type (max w w')), P.IsClosedUnderColimitsOfShape (Discrete J)) :
    (∀ (I : Type w), P.IsClosedUnderColimitsOfShape (Discrete I)) ∧
    (∀ (I : Type w) (X : I → C) (L : C) (ι : ∀ i, X i ⟶ L),
      Nonempty (IsColimit (Cofan.mk L ι)) ↔
        Nonempty (IsColimit
          (Cofan.mk (f := fun j : ULift.{w'} I ↦ X j.down) L (fun j ↦ ι j.down)))) ∧
    (∀ (I : Type w) (G : Discrete I ⥤ P.FullSubcategory),
      HasColimit (G ⋙ P.ι) →
        Nonempty (CreatesColimit G P.ι) ∧ PreservesColimit G P.ι ∧
          ReflectsColimit G P.ι ∧ HasColimit G) ∧
    (HasCoproducts.{w} C → HasCoproducts.{w} P.FullSubcategory) := by
  classical
  have hsmall (I : Type w) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    let := hP (ULift.{w'} I)
    exact ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence Equiv.ulift)
  refine ⟨hsmall, ?_, ?_, ?_⟩
  · intro I X L ι
    exact ⟨fun ⟨h⟩ ↦ ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk L ι) h⟩,
      fun ⟨h⟩ ↦ ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk L ι)).symm h⟩⟩
  · intro I G hG
    let := hsmall I
    let := hG
    let := createsColimitFullSubcategoryInclusionOfClosed (Discrete I) P G
    exact ⟨⟨inferInstance⟩, inferInstance, inferInstance, hasColimit_of_created G P.ι⟩
  · intro hC I
    let := hC
    let := hsmall I
    infer_instance

/-- The canonical restriction preserves inherited coproducts, has the ambient comparison map,
and is exact whenever the ambient functor and the inherited triangulations are exact.
Source: blueprint `det-proper-image-localizing-open`, Formal properties and Localizing
categories; Stacks Tags 002F, 05QM, 05QX, 014V
(blueprint: lem-sf-full-subcategory-universe-coproduct-lift).

Proof:
4. The functor is Mathlib's `Q.lift (P.ι ⋙ F)`, with its actual ambient objects and maps;
`Q.liftCompιIso` identifies its composite with the inclusion with `P.ι ⋙ F`. For a diagram
whose ambient coproduct exists, the source inclusion preserves its colimit by steps 1--3,
then `F` preserves it, and the target inclusion reflects it. Thus the restriction preserves
that coproduct. If the ambient source has all small coproducts this applies to every diagram.
5. For source and target inherited colimit cocones, the restricted comparison is the unique
arrow whose composites with the target legs are the images of the source legs. Its ambient
image satisfies precisely the same equations, so it equals the ambient comparison. It is
invertible since both cocones are colimiting after applying the restriction. This argument
also covers empty diagrams, when the universal property is initiality.
6. With the additional triangulated structures, use the inherited shift on each full
subcategory and the restricted shift isomorphisms of `F`. The inclusion detects distinguished
triangles, so the restricted functor is exact. Mathlib's `ObjectProperty.isTriangulated_lift`
applied to `P.ι ⋙ F` gives exactly this structure; `liftCompιIso` respects the shifts. No
assertion about generators or localizing closure enters this argument.
-/
theorem fullSubcategory_universe_coproduct_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]
    (hP : ∀ (J : Type (max w w')), P.IsClosedUnderColimitsOfShape (Discrete J))
    (hQ : ∀ (J : Type (max w w')), Q.IsClosedUnderColimitsOfShape (Discrete J))
    (F : C ⥤ D) (hF : ∀ (I : Type w), PreservesColimitsOfShape (Discrete I) F)
    (hPQ : ∀ (X : C), P X → Q (F.obj X)) :
    (Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property) ⋙ Q.ι = P.ι ⋙ F) ∧
    (∀ (I : Type w) (G : Discrete I ⥤ P.FullSubcategory),
      HasColimit (G ⋙ P.ι) →
        PreservesColimit G (Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property))) ∧
    (HasCoproducts.{w} C → ∀ (I : Type w),
      PreservesColimitsOfShape (Discrete I)
        (Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property))) ∧
    (∀ (I : Type w) (G : Discrete I ⥤ P.FullSubcategory),
      HasColimit (G ⋙ P.ι) → ∀ (c : Cocone G), Nonempty (IsColimit c) →
        ∀ (d : Cocone (G ⋙ Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)))
          (hd : IsColimit d),
          ∃ (hd' : IsColimit (Q.ι.mapCocone d)),
            Q.ι.map (hd.desc
              ((Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)).mapCocone c)) =
                hd'.desc (F.mapCocone (P.ι.mapCocone c)) ∧
            IsIso (hd.desc
              ((Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)).mapCocone c))) ∧
    (∀ [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
      [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
      [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
      [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
      [P.IsTriangulated] [Q.IsTriangulated] [F.CommShift ℤ] [F.IsTriangulated],
      (Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)).IsTriangulated ∧
        NatTrans.CommShift
          (Q.liftCompιIso (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)).hom ℤ) := by
  classical
  let H := Q.lift (P.ι ⋙ F) (fun X ↦ hPQ X.obj X.property)
  have hsmallP := (fullSubcategory_universe_coproduct_inheritance.{w, w'} P hP).1
  have hsmallQ := (fullSubcategory_universe_coproduct_inheritance.{w, w'} Q hQ).1
  have hpres (I : Type w) (G : Discrete I ⥤ P.FullSubcategory)
      (hG : HasColimit (G ⋙ P.ι)) : PreservesColimit G H := by
    let := hsmallP I
    let := hG
    let := hF I
    let := createsColimitFullSubcategoryInclusionOfClosed (Discrete I) P G
    let : PreservesColimit G (H ⋙ Q.ι) :=
      inferInstanceAs (PreservesColimit G (P.ι ⋙ F))
    exact preservesColimit_of_reflects_of_preserves H Q.ι
  refine ⟨rfl, hpres, ?_, ?_, ?_⟩
  · intro hC I
    let := hC
    exact ⟨fun {G} ↦ hpres I G inferInstance⟩
  · intro I G hG c ⟨hc⟩ d hd
    let := hG
    let := hF I
    let := hsmallQ I
    let := hpres I G hG
    let : HasColimit ((G ⋙ H) ⋙ Q.ι) :=
      inferInstanceAs (HasColimit ((G ⋙ P.ι) ⋙ F))
    let := createsColimitFullSubcategoryInclusionOfClosed (Discrete I) Q (G ⋙ H)
    let hd' := isColimitOfPreserves Q.ι hd
    refine ⟨hd', ?_, (hd.nonempty_isColimit_iff_isIso_desc).mp
      ⟨isColimitOfPreserves H hc⟩⟩
    apply hd'.hom_ext
    intro j
    change Q.ι.map (d.ι.app j) ≫ Q.ι.map (hd.desc (H.mapCocone c)) = _
    rw [← Q.ι.map_comp, hd.fac]
    exact (hd'.fac (F.mapCocone (P.ι.mapCocone c)) j).symm
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨inferInstance, inferInstance⟩

end CategoryTheory
