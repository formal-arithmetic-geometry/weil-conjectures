/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.Paper.FiniteSplitEtaleHypercover

/-!
# The universal property of hypercover cohomology

Source: Stacks Project, Hypercoverings, Sections 25.9–25.10, Tag 01H0.
(blueprint: def-weil-pbc-hypercover-cohomology-colimit)

The colimit is specified by its universal property, without choosing a skeleton of the
category of hypercovers. Homotopy invariance makes this exactly the colimit over refinements
modulo simplicial homotopy. The coefficient category may be abelian groups or modules.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type w) [Category.{v} A] [Abelian A]

/-- Cohomology of a hypercover as a functor of its coefficient sheaf. Evaluation uses
`F(U_n)`, with the alternating coface differential. For abelian groups this evaluates to
`FiniteSplitEtaleHypercover.cohomology`. For modules it computes homology in `ModuleCat`.
Source: Stacks 01H0; blueprint order 949.
(blueprint: def-weil-pbc-hypercover-cohomology-colimit) -/
noncomputable def cohomologyFunctor (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).obj U.simplicial.rightOp ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q

/-- The cohomology map induced contravariantly by a refinement. Each component is the
homology map of the cochain map whose degree `n` is restriction along `f_n`.
Source: Stacks Hypercoverings, Section 25.9, and Tag 01H0.
(blueprint: def-weil-pbc-hypercover-cohomology-colimit) -/
noncomputable def cohomologyRefinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) (q : ℕ) : cohomologyFunctor A V q ⟶ cohomologyFunctor A U q :=
  whiskerRight
    (whiskerLeft (sheafToPresheaf X.smallEtaleTopology A)
      ((whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).map f.rightOp))
    (AlgebraicTopology.alternatingCofaceMapComplex A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q)

/-- `H` is the natural colimit of degree-`q` cohomology over finite split hypercovers,
with refinements identified modulo simplicial homotopy. The maps `c` are natural in the
coefficient sheaf, commute with every refinement, and are a colimit cocone at every sheaf.
The first clause ensures that the diagram descends to homotopy classes; compatible families
on raw refinements and on their homotopy classes are then the same families.
Source: Stacks Hypercoverings, Section 25.9, Tag 01H0; blueprint order 949.
(blueprint: def-weil-pbc-hypercover-cohomology-colimit) -/
def IsCohomologyColimit (q : ℕ) (H : Sheaf X.smallEtaleTopology A ⥤ A) : Prop :=
  (∀ (U V : FiniteSplitEtaleHypercover X) (f g : U.Refinement V),
    isRefinementHomotopic f g → cohomologyRefinement A f q = cohomologyRefinement A g q) ∧
  ∃ c : ∀ U : FiniteSplitEtaleHypercover X, cohomologyFunctor A U q ⟶ H,
    (∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V),
      cohomologyRefinement A f q ≫ c U = c V) ∧
    ∀ (F : Sheaf X.smallEtaleTopology A) (B : A)
      (d : ∀ U : FiniteSplitEtaleHypercover X, (cohomologyFunctor A U q).obj F ⟶ B),
      (∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V),
        (cohomologyRefinement A f q).app F ≫ d U = d V) →
      ∃! e : H.obj F ⟶ B, ∀ U : FiniteSplitEtaleHypercover X, (c U).app F ≫ e = d U

end AlgebraicGeometry.FiniteSplitEtaleHypercover
