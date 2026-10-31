/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementData
import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementNormalization

/-! # ProjectionRefinementSquare -/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ProjectionRefinementDescent

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  projectionMapOfCompactification
  AlgebraicGeometry.ProEtale.derivedTensor theta
  AmbientProperOpen.RefinementProjection.finiteComparison

attribute [local implicit_reducible] tensorInput derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem native_component_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y) :
    ((AmbientProperOpen.RefinementProjection.finiteProjection A c).app K).app L =
      coefficientProjectionComponent A c K L := by
  rfl

private theorem invert_square
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F : A ⥤ B) {a b : A} {x y : B} (s : a ≅ b) (t : x ≅ y)
    (p : F.obj a ⟶ x) (q : F.obj b ⟶ y)
    (h : q ≫ t.inv = F.map s.inv ≫ p) :
    p ≫ t.hom = F.map s.hom ≫ q := by
  apply (cancel_epi (F.map s.inv)).mp
  calc
    F.map s.inv ≫ (p ≫ t.hom) = q := by
      rw [← Category.assoc, ← h]
      simp
    _ = F.map s.inv ≫ (F.map s.hom ≫ q) := by simp

private theorem invert_coefficient_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c d : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y)
    (s : (coefficientImage A c).obj K ≅ (coefficientImage A d).obj K)
    (t : (coefficientImage A c).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)) ≅
      (coefficientImage A d).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)))
    (h : (coefficientProjectionComponent A d K L) ≫
        t.inv = ((ProperOpenTensor A Y).map s.inv).app L ≫
          (coefficientProjectionComponent A c K L)) :
    (coefficientProjectionComponent A c K L) ≫
        t.hom = ((ProperOpenTensor A Y).map s.hom).app L ≫
          (coefficientProjectionComponent A d K L) := by
  exact invert_square ((ProperOpenTensor A Y).flip.obj L) s t
    ((coefficientProjectionComponent A c K L))
    ((coefficientProjectionComponent A d K L)) h

/-- The witnessed projection square for a single arbitrary proper refinement.
Source: lem-sf-projection-refinement-descent, steps 4--7; Stacks 0F7B, 0F7G,
0B56 and 0DV0.
(blueprint: lem-sf-projection-refinement-square).

Proof: use refinementProjectionCounit, whose finite clause proves the projection
square for the directed, un-inverted proper/open mate on arbitrary unbounded
inputs. The normalized_refinement_inverse lemma identifies that directed map at K
and tensorInput with the inverse of each witnessed theta. Precompose the resulting
equation with the tensor of theta_K and postcompose with theta_T, cancelling the
two inverse pairs. This proves the required direction of refinementLaw. It uses
no Cartesian hypothesis and never inverts a projection morphism; identity
refinements and zero inputs obey the same equation. -/
theorem refinement_square
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (r : c.Refinement d)
    (K : (boundedConstructible C.l E n X).FullSubcategory)
    (L : (finiteTor C.l E n Y).FullSubcategory) :
    refinementLaw C.l E n c d r K L := by
  intro O e OT eT
  let X' : AmbientProperOpen.Spaces D :=
    ⟨⟨X, ⟨⟨⟩⟩, X ↘ Spec (.of D.k)⟩, inferInstanceAs (LocallyOfFiniteType
      (X ↘ Spec (.of D.k))), inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))⟩
  let Y' : AmbientProperOpen.Spaces D :=
    ⟨⟨Y, ⟨⟨⟩⟩, Y ↘ Spec (.of D.k)⟩, inferInstanceAs (LocallyOfFiniteType
      (Y ↘ Spec (.of D.k))), inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))⟩
  let f' : X' ⟶ Y' := ⟨⟨f, 𝟙 _, by
    change f ≫ (Y ↘ Spec (.of D.k)) = (X ↘ Spec (.of D.k)) ≫ 𝟙 _
    simpa only [Category.comp_id] using comp_over f (Spec (.of D.k))⟩⟩
  let : QuasiCompact f'.hom.left := by
    change QuasiCompact f
    infer_instance
  have h := (AmbientProperOpen.refinementProjectionCounit D C.l C.different E n
    (X := X') (Y := Y') (f := f') c d r).1 K.obj L.obj
  have hT := normalized_refinement_inverse D C E n (f := f') r
    (tensorInput C.l E n f'.hom.left K.obj L.obj) OT eT
  dsimp only [tensorInput] at hT
  have hK := normalized_refinement_inverse D C E n (f := f') r K.obj O e
  rw [native_component_eq, native_component_eq, ← hT, ← hK] at h
  dsimp only [tensorInput]
  dsimp only [X', Y', f', ObjectProperty.homMk, Over.homMk,
    CostructuredArrow.homMk, Over.mk, CostructuredArrow.mk, Over.left, Over.Hom.left] at h
  exact invert_coefficient_square (Coefficient C.l E n) c d K.obj L.obj
    (theta C.l E n r K.obj O e)
    (theta C.l E n r (tensorInput C.l E n f K.obj L.obj) OT eT) h

end WeilConjectures.ProjectionRefinementDescent
