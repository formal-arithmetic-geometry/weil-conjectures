/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.InternalHomOverEquiv

/-! # Transport of ordinary evaluation across the open-site equivalence
Source: Stacks Project, Tags 08DL, 08DJ and 08DQ; Mathlib `Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-over-transport).
This is a statement about actual complexes only. It mentions neither RHom nor
canonical derived evaluation nor an arbitrary derived representative.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Transport the ordinary tensor and Hom models, and their component equation.
Source: Stacks Project, Tags 08DL, 08DJ and 08DQ, ordinary complex constructions.
(blueprint: lem-pc-ordinary-evaluation-over-transport).

Proof: use the functor of Modules.overEquiv U degreewise. Reindexing the sheaves
preserves unit action and module tensor: on local sections the map takes a pure
tensor to the same pure tensor. The unit comparison identifies the transported
single complex with the single unit on U.toScheme. The internal Hom comparison
reindexes local linear maps (internalHom_overEquiv). Preservation of products
extends it to Hom degrees; naturality with pre- and postcomposition identifies the
Hom differentials. Preservation of coproducts extends the tensor comparison to
total degrees; additivity identifies both signed differentials. Their composite
gives the two chain isomorphisms below, in the displayed orientations. Reindexing
is exact and its inverse is exact, so it preserves acyclic complexes and
quasi-isomorphisms. The Hom comparisons and this exact inverse transport hhom.
Tensor comparisons in both directions transport the K-flat acyclicity criterion.
The exact inverse and the Hom homotopy comparisons transport K-injectivity of F.
Finally precompose by each tensor inclusion and postcompose by each Hom projection.
The transported formula is unchanged: when r+q=0 it is unit action on the evaluated
functional, and otherwise it is zero. This is exactly IsSchemeOrdinaryEvaluation.
Zero complexes and the empty open satisfy the same universal-property argument. -/
theorem exists_ordinaryEvaluation_over_transport (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (hdual : (localEvaluationDual X U P).IsKFlat)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) [F.IsKInjective] :
    let L := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    let P' := T.obj P
    let F' := T.obj F
    let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    let D' := homComplex (R := U.toScheme.sheaf) P' O'
    ∃ t : T.obj (localEvaluationTensor X U P F) ≅ pullbackTensorTotal U.toScheme F' D',
      ∃ b : T.obj (homComplex (R := X.sheaf.over U) P F) ≅
          homComplex (R := U.toScheme.sheaf) P' F',
        (∀ (M M' : CochainComplex
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ) (a : M ⟶ M'),
          QuasiIso a →
            QuasiIso (((homComplexFunctor (R := U.toScheme.sheaf)).obj (op P')).map a)) ∧
        D'.IsKFlat ∧ CochainComplex.IsKInjective F' ∧
        IsSchemeOrdinaryEvaluation U.toScheme P' F' (t.inv ≫ T.map f ≫ b.hom) := by sorry

end AlgebraicGeometry
