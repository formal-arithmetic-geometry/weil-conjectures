/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! Natural comparison transformation for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-core) -/

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

/-- A natural comparison with the specified K-flat representative equation, without an
invertibility assertion.

Proof: identify the composite stalk ring map with the actual stalk map of g'.
On K-flat sheaf complexes use the scalar-extension counit, the Q/Qh factors,
the specified tensorStalkIso, the inverse exact-stalk factor and the inverse
pullback counit in the displayed order. Exact stalks preserve quasi-isomorphisms,
and their K-flatness follows from the stalk criterion. Naturality of the counits
and the degreewise pullback-stalk identification gives naturality for chain maps
between K-flat representatives. Every derived arrow is represented by a roof;
replace its middle complex by a K-flat resolution. Common refinements show the
induced maps are independent of the roof and resolution. They therefore descend
to a natural transformation on derived categories. For a K-flat P with invertible
pullback counit use P itself as its resolution; the construction is precisely the
stated equation. Invertibility of this transformation is a separate argument.
Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 (Tag 0DJ7);
Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison-core). -/
theorem exists_stalkDerivedExtensionComparisonTransformation (z : X') :
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
    ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ⟶
        derivedPullback g' ⋙ comparisonDerivedStalk X' z,
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlat)
        (hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.app (DerivedCategory.Q.obj P) =
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
              (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
