/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
import Sheaf.AlgebraicGeometry.InternalHomOverEquiv
import Sheaf.AlgebraicGeometry.TotalTensorOverEquivIso

/-! # Compatible ordinary evaluation comparisons on the open scheme

Source: Stacks Project, Tags 08DL, 08DJ and 08DQ, ordinary complex constructions.
(blueprint: lem-pc-ordinary-evaluation-over-comparisons).
No acyclicity, quasi-isomorphism or K-injectivity assertion is included here. -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Compatible comparisons for ordinary Hom, its dual and ordinary evaluation.
Source: Stacks Project, Tags 08DL, 08DJ and 08DQ; Mathlib `Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-over-comparisons).

Proof: apply `internalHom_overEquiv` to each pair of terms of P and M. Take the
product comparison in each Hom degree, using the specified projections of
`homComplex_projections_exists`. The naturality equation for internal Hom and
additivity identify the differential d_M phi - (-1)^n phi d_P on both sides.
This yields b M, natural in M by checking after each Hom projection. At M equal
to the single unit, compose b M with Hom(P',-) applied to the chain isomorphism
from the transported single unit to the scheme single unit; call this composite d.
For each F, apply the total tensor comparison and then tensor with d to obtain t.
Use these same comparisons, rather than unrelated isomorphisms, for all three maps.
To check evaluation, precompose with each tensor summand and postcompose with each
Hom projection. When r+q=0, both composites curry the same sectionwise map
(y,phi,x) -> y*phi(x): reindexing commutes with composition and with the unit
action. The associator, symmetry and unit comparison used in d are the comparisons
of these same sectionwise maps.
When r+q is nonzero, the projection to the single unit in that degree vanishes,
so both evaluation components are zero. Naturality of degree-equality
isomorphisms identifies the final output degrees. The product and coproduct
universal properties give the claimed component equation for every f satisfying
the local formula. These constructions require no homological assumptions on P
or F, and apply equally to zero complexes and the empty open. -/
theorem exists_ordinaryEvaluation_over_comparisons (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    let P' := T.obj P
    let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    let D' := homComplex (R := U.toScheme.sheaf) P' O'
    ∃ b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
        T.obj (homComplex (R := X.sheaf.over U) P M) ≅
          homComplex (R := U.toScheme.sheaf) P' (T.obj M),
      (∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
        T.map (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a) ≫
            (b N).hom =
          (b M).hom ≫
            ((homComplexFunctor (R := U.toScheme.sheaf)).obj (op P')).map (T.map a)) ∧
      ∃ d : T.obj (localEvaluationDual X U P) ≅ D',
        ∀ F : CochainComplex (localEvaluationModules X U) ℤ,
          ∃ t : T.obj (localEvaluationTensor X U P F) ≅
              pullbackTensorTotal U.toScheme (T.obj F) D',
            ∀ f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F,
              IsLocalOrdinaryEvaluation X U P F f →
                IsSchemeOrdinaryEvaluation U.toScheme P' (T.obj F)
                  (t.inv ≫ T.map f ≫ (b F).hom) := by sorry

end AlgebraicGeometry
