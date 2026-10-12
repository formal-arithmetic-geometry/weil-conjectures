/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Comparison of étale and pro-étale global cohomology

For a scheme `X` and a bounded below complex `K` of étale sheaves on `X`, the derived unit
`K ⟶ Rν_* ν^* K` of the comparison adjunction `ν^* ⊣ ν_*` induces an isomorphism
`RΓ(X_ét, K) ≅ RΓ(X_proét, ν^* K)` (`AlgebraicGeometry.ProEtale.rightDerivedSectionsComparisonIso`,
blueprint `lem-weil-pbc-comparison-global-cohomology`): the global sections of a pro-étale sheaf
are the global sections of its restriction `ν_*`, which preserves injectives, so that
`RΓ(X_proét, -) ≅ RΓ(X_ét, -) ∘ Rν_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The restriction `ν_*` preserves injective objects, being right adjoint to the exact functor
`ν^*`. -/
instance preservesInjectiveObjects_comparisonLowerStar :
    (comparisonLowerStar A X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (comparisonAdjunction A X)

/-- The derived unit `K ⟶ Rν_* ν^* K` of the comparison adjunction is an isomorphism on the bounded
below derived category of étale sheaves. -/
instance isIso_comparisonAdjunction_derivedPlus_unit :
    IsIso (comparisonAdjunction A X).derivedPlus.unit := by
  have := isIso_comparisonAdjunction_unit A X
  exact NatIso.isIso_of_isIso_app _ |>.mpr fun K ↦
    (comparisonAdjunction A X).isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun _ _ ↦ inferInstance) (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A X I) K

/-- The derived global sections of the pro-étale site factor through the derived restriction:
`RΓ(X_proét, -) ≅ RΓ(X_ét, -) ∘ Rν_*` on bounded below complexes, since the global sections of a
pro-étale sheaf are those of its restriction to the étale site and `ν_*` preserves injectives. -/
noncomputable def rightDerivedComparisonLowerStarCompSectionsIso :
    R+(ν_*(X)[A]) ⋙ R+(Etale.sectionsFunctor A X) ≅ R+(globalSectionsFunctor A X) :=
  Functor.rightDerivedFunctorPlusCompIso' (comparisonLowerStar A X)
    (Etale.sectionsFunctor A X) (Iso.refl _)

/-- Blueprint `lem-weil-pbc-comparison-global-cohomology`: comparison of global cohomology.

For a bounded below complex `K` of étale sheaves, the derived unit `K ⟶ Rν_* ν^* K` induces a
natural isomorphism `RΓ(X_ét, K) ≅ RΓ(X_proét, ν^* K)` of the ordinary derived global sections. -/
noncomputable def rightDerivedSectionsComparisonIso :
    R+(Etale.sectionsFunctor A X) ≅ D+(ν^*(X)[A]) ⋙ R+(globalSectionsFunctor A X) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (comparisonAdjunction A X).derivedPlus.unit)
      R+(Etale.sectionsFunctor A X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+(ν^*(X)[A]) (rightDerivedComparisonLowerStarCompSectionsIso A X)

/-- The isomorphism `RΓ(X_ét, K) ≅ RΓ(X_proét, ν^* K)` of
`AlgebraicGeometry.ProEtale.rightDerivedSectionsComparisonIso` is induced by the derived unit
`K ⟶ Rν_* ν^* K`. -/
lemma rightDerivedSectionsComparisonIso_hom_app (K : DerivedCategory.Plus
    (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedSectionsComparisonIso A X).hom.app K =
      R+(Etale.sectionsFunctor A X).map ((comparisonAdjunction A X).derivedPlus.unit.app K) ≫
        (rightDerivedComparisonLowerStarCompSectionsIso A X).hom.app
          (D+(ν^*(X)[A]).obj K) := by
  simp [rightDerivedSectionsComparisonIso]

end AlgebraicGeometry.ProEtale
