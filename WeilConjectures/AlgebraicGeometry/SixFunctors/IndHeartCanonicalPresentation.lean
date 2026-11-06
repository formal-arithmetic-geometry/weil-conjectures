/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Canonical presentations of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`sk-prop-ind-heart-canonical-presentation.md` and its proof
(blueprint: det-ind-heart-canonical-presentation).

`CostructuredArrow` is exactly the category of constructible modules mapping to B.
`Functor.isDenseAt` asserts the colimit property for its tautological cocone, whose
leg at (C,c) is c. Small diagrams and essential smallness use universe u+1, as in
`IndHeartFullFaithfulnessAssertions` and def-weil-size-convention. The universal property
over the full essentially small category is equivalent to the one over a small skeleton.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical-presentation assertions for the coefficient ring object Λ on X.
Here IndCons is the replete filtered-colimit closure `ObjectProperty.ind`, as in
`det-ind-heart-full-faithfulness`. The category J(B) is the existing costructured-arrow
category of the constructible inclusion. Density at B means precisely that the cocone
with legs c at (C,c) is a colimit, rather than just that some colimit object is isomorphic
to B. The final clause applies to every small filtered constructible colimit presentation,
with the functor to J(B) induced by its specified cocone legs.
Source: blueprint sk-prop-ind-heart-canonical-presentation.md, entire statement
(blueprint: det-ind-heart-canonical-presentation). -/
def IndHeartCanonicalPresentationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
    EssentiallySmall.{u + 1}
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    IsFiltered
      (CostructuredArrow (ObjectProperty.ι (IsConstantModelConstructible Λ X)) B) ∧
    (ObjectProperty.ι (IsConstantModelConstructible Λ X)).isDenseAt B ∧
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (pres : ObjectProperty.ColimitOfShape (IsConstantModelConstructible Λ X) I B),
      pres.toCostructuredArrow.Final

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cofinality argument for a filtered presentation by finitely presentable objects.
Source: canonical-presentation proof, Cofinality paragraph.
(blueprint: det-ind-heart-canonical-presentation). -/
private theorem final_constructiblePresentation
    {C : Type*} [Category.{u + 1} C] (P : ObjectProperty C)
    (hP : ∀ A : P.FullSubcategory, IsFinitelyPresentable.{u + 1} A.obj)
    {B : C} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (pres : P.ColimitOfShape I B) : pres.toCostructuredArrow.Final := by
  classical
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro f
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit f.hom
    exact ⟨i, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
  · intro f i g h
    have : IsFinitelyPresentable.{u + 1} (P.ι.obj f.left) := hP f.left
    obtain ⟨j, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit pres.isColimit
      g.left.hom h.left.hom ((CostructuredArrow.w g).trans (CostructuredArrow.w h).symm)
    refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    change g.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) =
      h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b)
    calc
      _ = (g.left.hom ≫ pres.diag.map a) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = (h.left.hom ≫ pres.diag.map b) ≫ pres.diag.map (IsFiltered.coeqHom a b) := by
        rw [hab]
      _ = h.left.hom ≫ pres.diag.map (b ≫ IsFiltered.coeqHom a b) := by
        rw [pres.diag.map_comp, Category.assoc]
      _ = h.left.hom ≫ pres.diag.map (a ≫ IsFiltered.coeqHom a b) := by
        rw [IsFiltered.coeq_condition a b]

end AlgebraicGeometry.ProEtale
