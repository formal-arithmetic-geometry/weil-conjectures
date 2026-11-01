/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Functor

/-! # Evaluation and homology of complexes of functors

Source: Stacks Project, Homology, Tag 0130. Exact evaluation commutes with
homology, naturally both in the diagram variable and in the complex.
(blueprint: new-finite-cover-functor-homology-evaluation)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uK vK uC vC uI

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {K : Type uK} [Category.{vK} K] {C : Type uC} [Category.{vC} C]
  [Abelian C] {I : Type uI} {c : ComplexShape I}
  (J : HomologicalComplex (K ⥤ C) c)

/-- The evaluation comparison for homology of a complex of functors.
Source: Stacks Project, Tag 0130. The evaluation functor is exact, so it
preserves the kernel and cokernel defining homology.
(blueprint: new-finite-cover-functor-homology-evaluation) -/
def homologyEvaluationIso (q : I) (x : K) :
    (J.asFunctor.obj x).homology q ≅ (J.homology q).obj x :=
  (J.sc q).mapHomologyIso ((evaluation K C).obj x)

/-- Computing homology pointwise is natural in the diagram variable.
Source: Stacks Project, Tag 0130. Apply the homology comparison formula to the
natural transformation between evaluation functors induced by a morphism in `K`.
(blueprint: new-finite-cover-functor-homology-evaluation) -/
def homologyAsFunctorIso (q : I) :
    J.asFunctor ⋙ homologyFunctor C c q ≅ J.homology q :=
  NatIso.ofComponents (J.homologyEvaluationIso q) (fun {x y} g ↦ by
    rw [← cancel_epi (J.homologyEvaluationIso q x).inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (NatTrans.app_homology ((evaluation K C).map g) (J.sc q)).symm)

/-- Naturality of the evaluation comparison in a morphism of complexes.
Source: Stacks Project, Tag 0130. This is naturality of the homology comparison
for the fixed exact evaluation functor.
(blueprint: new-finite-cover-functor-homology-evaluation) -/
theorem homologyEvaluationIso_hom_naturality
    {J' : HomologicalComplex (K ⥤ C) c} (φ : J ⟶ J') (q : I) (x : K) :
    homologyMap ((complexOfFunctorsToFunctorToComplex.map φ).app x) q ≫
        (J'.homologyEvaluationIso q x).hom =
      (J.homologyEvaluationIso q x).hom ≫ (homologyMap φ q).app x := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (K ⥤ C) c q).map φ) ((evaluation K C).obj x)

end HomologicalComplex
