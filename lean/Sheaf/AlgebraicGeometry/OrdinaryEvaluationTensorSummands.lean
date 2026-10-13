/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Normalized tensor summands under the open-site equivalence

Source: Stacks Project, Tag 0A8X, ordinary tensor totalization; the open-site
reindexing construction in Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

noncomputable local instance ordinarySummandOverPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

noncomputable local instance ordinarySummandSchemePreadditive (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1

/-- The open-site tensor comparison has the prescribed unit, symmetry and total summands.
Source: Stacks Project, Tag 0A8X, tensor totalization; Mathlib `overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands).

Proof: on presheaves reindex each pure tensor along the open-site equivalence.
The coefficient identifications preserve balancing, restriction, associativity
and exchange of factors. Descend these maps and their inverses through
sheafification. The unit map sends a local coefficient to the same coefficient;
this is `overEquivFunctorObjUnitIso`. This constructs a symmetric monoidal
structure m with that unit, rather than an arbitrary natural tensor comparison.
In bidegree (p,q) use the inverse of m's tensorator. Its naturality commutes
with both differentials. Assemble the bicomplex isomorphism and compose its
totalization with the inverse of `HomologicalComplex₂.mapTotalIso`.
The equivalence preserves all coproducts, so the image of every total summand
is exactly the displayed tensorator followed by its target summand inclusion.
This gives c and its equation. Signed differentials introduce no additional
sign in these degreewise inclusions. This construction applies to unbounded
complexes, zero modules, the empty open and the zero coefficient ring. -/
theorem exists_ordinaryEvaluation_tensor_summands (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) ∧
      ∀ P F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ (p q n : ℤ) (h : p + q = n),
            L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
                (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
              (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
                HomologicalComplex.ιMapBifunctor (T.obj F)
                  (T.obj (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ) p q n h := by sorry

end AlgebraicGeometry
