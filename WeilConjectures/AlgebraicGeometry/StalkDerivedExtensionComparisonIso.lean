/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso

/-! Intermediate comparison isomorphism for the derived stalk extension.

## References

* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

-- Keep the existing quantified proof-binder names unchanged.
set_option linter.unusedVariables false in
/-- Derived pullback commutes with exact stalks, with its comparison specified before
applying homology. This statement assumes a universal scalar-extension pair; it does
not construct that pair or assert invertibility of its counit on stalk complexes. -/
theorem exists_stalkDerivedExtensionComparisonIso (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∀ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
      DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh)
      (hL : L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ))),
    ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ≅
        derivedPullback g' ⋙ comparisonDerivedStalk X' z,
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.hom.app (DerivedCategory.Q.obj P) =
          L.map ((DerivedCategory.quotientCompQhIso _).inv.app (stalkComplex g' z P)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P)) ≫
            DerivedCategory.Qh.map
              (((ModuleCat.extendScalars.{u, u, u}
                ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
                  (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app
                (stalkComplex g' z P)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
              (tensorComplex f f' g g' sq z P) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
            (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.inv.app
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ≫
            (comparisonDerivedStalk X' z).map
              (cast (by rfl)
                (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  intro L ε hL
  obtain ⟨j, hj⟩ := exists_stalkDerivedExtensionComparisonTransformation f f' g g' sq z L ε hL
  have : IsIso j := stalkDerivedExtensionComparison_isIso f f' g g' sq z L ε hL j hj
  exact ⟨asIso j, hj⟩


end AlgebraicGeometry.SingleComplexBaseChange
