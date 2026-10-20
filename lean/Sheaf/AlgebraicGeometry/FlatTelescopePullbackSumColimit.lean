/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import Sheaf.CategoryTheory.DerivedCountableSumsExact

/-! # Pullback of the source coproduct in a flat telescope

Source: Stacks Tags 06YS and 06YJ, sum step of the telescope normalization plan.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Derived pullback of a complex sum, and of its translate, gives the coproduct
of the corresponding stage images. No flatness or boundedness is required.

Source: Stacks Tag 07D9, Injectives, direct sums in derived categories, and Tag 079W,
Cohomology, derived pullback adjunction. Sum step of
lem-sc-flat-telescope-normalization-morphisms.

Proof. Sheaf modules have K-injective resolutions. Represent any target by a
K-injective complex. Each derived map from a stage lifts to a chain map into this
representative, by bijectivity of Qh on maps into K-injectives and surjectivity of
the homotopy quotient. The coproduct of complexes assembles these chain maps.
Two factorizations equal on all stages have homotopies on each stage; the degreewise
coproduct universal property assembles these into a homotopy on the sum. Thus Q of
the sum has the coproduct universal property, with the prescribed inclusions.
Derived pullback is left adjoint to derived direct image and preserves the cofan.
Transport along quotientCompQhIso to the homotopy-localization formulation.
For the translated cofan use the Qh shift comparison, preservation of coproducts
by the derived shift equivalence, and preservation by derived pullback again.
Zero stages and the zero category on an empty scheme are included.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/
theorem flat_telescope_pullback_sum_colimit
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    let L := DerivedCategory.Qh
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⋙ derivedPullback f
    Nonempty (IsColimit (Cofan.mk (f := fun n ↦ L.obj (q.obj (E n)))
      (L.obj (q.obj (∐ E)))
      (fun n ↦ L.map (q.map (Sigma.ι E n))))) ∧
    Nonempty (IsColimit (Cofan.mk (f := fun n ↦ L.obj ((q.obj (E n))⟦(1 : ℤ)⟧))
      (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧')))) := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := derivedPullback f
  have : IsGrothendieckAbelian.{u} A :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have : AB4OfSize.{u} A := IsGrothendieckAbelian.ab4OfSize A
  have : CountableAB4 A :=
    ⟨fun J _ ↦ HasExactColimitsOfShape.of_domain_equivalence A
      (Discrete.equivalence (Equiv.ulift : ULift.{u} J ≃ J))⟩
  -- Use the existing termwise-coproduct theorem before applying the left adjoint.
  have : PreservesColimit (Discrete.functor E) (DerivedCategory.Q : _ ⥤
      schemeDerivedCategory Y) :=
    preservesColimit_of_preserves_colimit_cocone
      (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor E))
      (DerivedCategory.isColimit_mapCocone_countableSum A ℕ E).some
  have : PreservesColimit (Discrete.functor E) (q ⋙ (DerivedCategory.Qh (C := A))) :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A).symm
  have : F.IsLeftAdjoint := (nonempty_derivedPullbackAdjunction f).some.isLeftAdjoint
  have hc := isColimitOfPreserves ((q ⋙ (DerivedCategory.Qh (C := A))) ⋙ F)
    (coproductIsCoproduct E)
  have hc₀ : IsColimit (Cofan.mk
      (f := fun n ↦ F.obj ((DerivedCategory.Qh (C := A)).obj (q.obj (E n))))
      (F.obj ((DerivedCategory.Qh (C := A)).obj (q.obj (∐ E))))
      (fun n ↦ F.map ((DerivedCategory.Qh (C := A)).map (q.map (Sigma.ι E n))))) :=
    Cofan.isColimitMapCoconeEquiv _ E _ hc
  let S := shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)
  have : PreservesColimit (Discrete.functor E) (q ⋙ S ⋙ (DerivedCategory.Qh (C := A))) := by
    let S' := shiftFunctor (schemeDerivedCategory Y) (1 : ℤ)
    have : PreservesColimit (Discrete.functor E) ((q ⋙ (DerivedCategory.Qh (C := A))) ⋙ S') :=
      inferInstance
    exact preservesColimit_of_natIso _
      ((Functor.associator q S (DerivedCategory.Qh (C := A))) ≪≫
        Functor.isoWhiskerLeft q ((DerivedCategory.Qh (C := A)).commShiftIso (1 : ℤ)) ≪≫
        (Functor.associator q (DerivedCategory.Qh (C := A)) S').symm).symm
  have hc' := isColimitOfPreserves ((q ⋙ S ⋙ (DerivedCategory.Qh (C := A))) ⋙ F)
    (coproductIsCoproduct E)
  refine ⟨⟨hc₀⟩, ⟨?_⟩⟩
  exact Cofan.isColimitMapCoconeEquiv _ E _ hc'

end AlgebraicGeometry
