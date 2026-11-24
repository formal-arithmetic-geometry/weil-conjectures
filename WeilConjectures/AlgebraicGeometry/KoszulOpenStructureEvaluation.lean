/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
import WeilConjectures.AlgebraicGeometry.KoszulOpenExponentOneUnit

/-! # Structure evaluation with a single Koszul normalization

## References

* Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Natural evaluation, normalized on the structure object by the exponent-one class. -/
theorem koszulOpen_structure_evaluation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    let c := fun e : ℕ ↦ H.map (koszulCechDerivedComparison A r f (koszulOpenSheafComplex A r f e))
        (H.map (DerivedCategory.Q.map (colimit.ι
          (koszulCechHomDiagram A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj
              (koszulOpenSheafComplex A r f e))) e))
          (koszulOpenHomStageClass A r f (koszulOpenSheafComplex A r f e) e (𝟙 _)))
    ∃ b : ∀ E : schemeDerivedCategory (Spec (.of A)),
      (R.obj (koszulOpenStructure A) ⟶ R.obj E) ≃ H.obj (G.obj E),
      (∀ (E E' : schemeDerivedCategory (Spec (.of A))) (g : E ⟶ E')
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E),
        b E' (ψ ≫ R.map g) = H.map (G.map g) (b E ψ)) ∧
      b (koszulOpenStructure A) (𝟙 _) =
        H.map (G.map (koszulOpenUnit A r f 0)) (c 0) := by
  obtain ⟨b, hb, hunit⟩ := derivedOpenStructure_evaluation_unit.{u, w, v}
    A (koszulOpen A r f)
  refine ⟨b, hb, ?_⟩
  exact hunit.trans (koszulOpen_exponent_one_unit.{u, w, v} A r f).symm

end AlgebraicGeometry
