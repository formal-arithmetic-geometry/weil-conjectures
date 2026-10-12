module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.Paper.AffinePerfectKoszulPrincipalUnit
import Sheaf.Paper.KoszulComplex

@[expose] public section
universe uMain wMain
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Intermediate representability and colimit assertion; source Tags 08DC and 08DD.
(blueprint: lem-sc-affine-perfect-open-represent-cohomology-colimit) -/
theorem affine_perfect_open_represent_cohomology_colimit
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    ∃ v : ∀ e : ℕ,
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenStructure A) ⟶
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenObject A r f e),
      (∀ e : ℕ,
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) ≫ v e = 𝟙 _) ∧
      (∀ e : ℕ, v e ≫
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) = 𝟙 _) ∧
      ∃ ι : koszulOpenHomDiagram A r f E.1 ⟶
        (Functor.const ℕ).obj
          (((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
              (koszulOpenStructure A) ⟶
           ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj E.1),
        (∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1),
          ι.app e φ = v e ≫
            ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                      (koszulOpen A r f)) ⋙
                    Equivalence.functor
                      (C := SheafOfModules.{uMain}
                        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                      (D := SheafOfModules.{uMain}
                        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map φ) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  sorry

end AlgebraicGeometry
