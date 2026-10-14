/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module
public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import Sheaf.AlgebraicGeometry.SchemeTensorUnitAction
/-! # Ordinary evaluation: a step of the chain calculation
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
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
/-- The ordinary component formula gives the tensor-unit action for a factor map.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, step 3.
(blueprint: lem-pc-scheme-ordinary-evaluation-chain-action).

Proof: The K-injective augmentation eta_O is monic degreewise. Consequently
the supplied factorization equation determines each component of e: on a
V^q tensor P^r summand it is symmetry followed by uncurrying the Hom(P,O)
projection. This follows by projection naturality and cancellation of eta_O.
Test the desired equality on F^p tensor V^q tensor P^r. Uncurry the formula
hf using the inverse laws of the tensor-Hom bijection and the symmetry.
When q+r is nonzero, O^(q+r) is zero and both components vanish. When q+r=0,
use singleObjXSelf to identify its coefficient with the unit. The resulting
map is the right unit action on F^p after tensoring with the component of e.
The standard total complex associator reindexes these same three summands
without a sign. Naturality in eta_F places its augmentation last. Apply
coproduct extensionality twice and then chain-map extensionality. The
argument works for all integer degrees and requires no flatness or boundedness;
it also holds for zero complexes and the empty scheme. -/
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
      schemeTensorUnitAction Y F V P e ≫ eta.app F := by sorry
end AlgebraicGeometry
