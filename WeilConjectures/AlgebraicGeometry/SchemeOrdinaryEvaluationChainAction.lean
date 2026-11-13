/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import WeilConjectures.AlgebraicGeometry.SchemeTensorUnitAction
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationTripleComponent
import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorUnitComponent
/-! # Ordinary evaluation: a step of the chain calculation

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- Prove tensor extensionality with abstract complexes, keeping coproduct data out of the
-- later component calculation on the concrete single-unit complex.
private theorem triple_ext {C : Type*} [Category* C] [Preadditive C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [HasColimitsOfSize.{0, 0} C] (F V P N : CochainComplex C ℤ)
    (a b : HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor F V (curriedTensor _) (.up ℤ)) P
        (curriedTensor _) (.up ℤ) ⟶ N)
    (h : ∀ (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k),
      (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
        ≫ HomologicalComplex.ιMapBifunctor
          (HomologicalComplex.mapBifunctor F V (curriedTensor _) (.up ℤ)) P
            (curriedTensor _) (.up ℤ) n r k hnr ≫ a.f k =
      (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
        ≫ HomologicalComplex.ιMapBifunctor
          (HomologicalComplex.mapBifunctor F V (curriedTensor _) (.up ℤ)) P
            (curriedTensor _) (.up ℤ) n r k hnr ≫ b.f k) : a = b := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r hh
  have hpqr : p + q + r = k := hh
  have hi := HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor _) (curriedTensor _) F V P (.up ℤ) (.up ℤ)
      p q r (p + q) k rfl hpqr
  simp only [curriedTensor_map_app] at hi
  rw [hi]
  exact (Category.assoc _ _ _).trans
    ((h p q r (p + q) k rfl hpqr).trans (Category.assoc _ _ _).symm)

/-- The ordinary component formula gives the tensor-unit action for a factor map. -/
theorem schemeOrdinaryEvaluation_chain_action (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f)
    (e : pullbackTensorTotal Y
      (homComplex (R := Y.sheaf) P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) P ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let phiF := f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F)
    let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
    schemeTensorHomUncurry Y V P O phiO = e ≫ eta.app O →
    schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F phiF =
      schemeTensorUnitAction Y F V P e ≫ eta.app F := by
  classical
  intro O V eta phiF phiO hO
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let := SheafOfModules.monoidalClosed (R := Y.sheaf)
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  apply triple_ext F V P ((schemeHomKInjectiveResolution Y).obj F)
  intro p q r n k hpq hnr
  have hu := schemeOrdinaryEvaluation_triple_component Y P F f hf p q r n k hpq hnr
  have ha := schemeCanonicalTensorUnit_component Y P F e p q r n k hpq hnr hO
  exact hu.trans ha.symm
end AlgebraicGeometry
