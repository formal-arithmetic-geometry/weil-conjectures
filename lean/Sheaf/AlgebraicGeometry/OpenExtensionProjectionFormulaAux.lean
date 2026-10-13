module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! Projection mate for transported open extension.
Source: Stacks Project, Tags 01AK, 06YB and 08BS.
(blueprint: lem-pc-open-extension-projection-formula). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance openExtensionProjectionStandardDerivedAux (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The projection mate is invertible for the transported adjunction.
Source: Stacks Project, Tags 01AK, 06YB and 08BS.
(blueprint: lem-pc-open-extension-projection-aux).
Proof: compute the mate after restriction using the adjunction hom-equivalence. The
unit and the monoidal comparison are invertible, and restriction reflects
isomorphisms on the supported objects arising from extension by zero. Hence the
mate is invertible for every object `A` and `K` and every strong monoidal structure. -/
theorem openExtension_projection_formula_of_adjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ (m : R.Monoidal),
      letI := m
      ∀ (J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adj : J ⊣ R),
        ∀ (A : schemeDerivedCategory U.toScheme) (K : schemeDerivedCategory X),
          IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
            ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
              (Functor.Monoidal.μIso R (J.obj A) K).hom)) := by
  sorry

end
end AlgebraicGeometry
