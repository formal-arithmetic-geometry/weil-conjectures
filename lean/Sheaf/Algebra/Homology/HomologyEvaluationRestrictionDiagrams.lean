/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions

/-! # Restriction comparisons for the cycle-evaluation diagram

Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: new-v2-homology-evaluation-restriction-diagrams). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Restriction identifies the cycle-evaluation diagram before choosing any evaluation
map on homology.

Source: Stacks Project, Tag 0A8X, the product differential of the Hom complex;
Tag 08DL, restriction of internal Hom. This is steps 1 and 2 of
new-e3-homology-evaluation-restriction-comparison, with the cycle comparisons explicit.
(blueprint: new-v2-homology-evaluation-restriction-diagrams).

Proof: Let F be restriction to V followed by localization over W. On each internal
Hom factor use the local-map identification, first along the open-site equivalence
for V and then along the iterated-slice equivalence for W. These identifications
are natural for pre- and postcomposition. F preserves products, so the fixed
product projections determine a unique degreewise isomorphism F(Hom(T,J)) -> Q
carrying each projection to its restricted local-map identification. Additivity
and the projection formula for the Hom differential show that these isomorphisms
form a chain isomorphism. F is exact, since localization is exact and the open-site
equivalence preserves all limits and colimits. Apply its kernel comparison and
homology comparison, followed by those of the chain isomorphism, to obtain c and a.
The kernel and cokernel universal properties give the fourth equation, the square
for the cycle-to-homology quotient. Apply the same exact comparisons to T and J.
Combine the internal-Hom identification with their cycle and homology isomorphisms
to obtain s, t, v and b. Naturality of internal Hom gives the second, third and
fifth equations, for target cycle inclusion, target homology quotient and source
homology quotient respectively. For the first equation use the projection identity
of the chain comparison, the naturality of the cycle inclusions, and internal-Hom
naturality. No evaluation morphism e is used here. All comparisons are induced by
universal properties, which also apply to empty opens and zero complexes. -/
theorem homologyEvaluation_restriction_diagrams (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (V : X.Opens) (W : V.toScheme.Opens) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let P := homComplex (R := X.sheaf) T J
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      A K n (-n) 0 (by omega)
    ∃ a : F.obj (P.homology n) ≅ Q.homology n,
      ∃ b : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.homology (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
      ∃ c : F.obj (P.cycles n) ≅ Q.cycles n,
      ∃ s : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.cycles 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.cycles 0),
      ∃ t : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.X 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.X 0),
      ∃ v : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.homology 0),
        F.map (P.iCycles n ≫ homologyEvaluationProjection X T J n ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 _)) ≫ t.hom =
          c.hom ≫ Q.iCycles n ≫ π ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (A.iCycles (-n)) (𝟙 _) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.iCycles 0)) ≫ t.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0)) ≫ v.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) ∧
        F.map (P.homologyπ n) ≫ a.hom = c.hom ≫ Q.homologyπ n ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _)) ≫
            v.hom = b.hom ≫ SheafOfModules.homObjMap
              (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) := by sorry

end CategoryTheory
