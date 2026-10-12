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

/-- Intermediate finite Koszul structural facts; source Tags 08CX and 08DC.
(blueprint: lem-sc-affine-perfect-open-represent-cohomology-core) -/
theorem affine_perfect_open_represent_cohomology_core
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    (∀ e : ℕ, ∃ δ : koszulOpenKoszulObject A r f e ⟶
      (koszulOpenObject A r f e)⟦(1 : ℤ)⟧,
      Triangle.mk (koszulOpenUnit A r f e) (koszulOpenKoszulUnit A r f e) δ ∈
        distTriang (schemeDerivedCategory (Spec (.of A)))) ∧
    (∀ e : ℕ, Scheme.IsPerfect (Spec (.of A)) (koszulOpenObject A r f e)) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      koszulOpenMap A r f a b h ≫ koszulOpenUnit A r f a = koszulOpenUnit A r f b) := by
  sorry

end AlgebraicGeometry
