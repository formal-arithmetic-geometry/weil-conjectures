/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.BaseDerivedTensorLocalizedNaturality

/-! # Derived scalar extension and the stalk of derived pullback

Source: Stacks Project, Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison).
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

/-- Derived extension of the original stalk identifies naturally with the stalk of
sheaf derived pullback. The computation on K-flat complexes uses precisely the
specified tensor-stalk isomorphism and the two universal counits.

Proof: derive extension along the actual stalk map A -> C using K-flat resolutions
of A-modules. The K-flat stalk criterion says that stalks of K-flat sheaf complexes
are K-flat A-complexes. Their ordinary scalar extensions therefore compute this
left-derived functor, with invertible universal counits. The natural pullback-stalk
isomorphism identifies their ordinary scalar extensions with stalks of ordinary
sheaf pullback. Its degreewise components are those specifying tensorStalkIso.
Both sides preserve quasi-isomorphisms on these resolving objects. Localize this
natural identification and its inverse on K-flat representatives to obtain the
natural isomorphism j. The two inverse identities descend from the identities on
complexes. Compatibility with the localization factors and universal counits gives
the displayed equation after taking homology; scalarExtensionHomologyIso contains
exactly the scalar-extension counit and its localization factors. Exactness of
stalks gives comparisonStalkHomologyIso on the sheaf side. No base-flatness or
invertibility of the base-derived cohomology comparison is involved.
Source: Stacks Project, Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison). -/
theorem exists_stalkDerivedExtensionComparison (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∃ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
          DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ)) ∧
      ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ≅
          derivedPullback g' ⋙ comparisonDerivedStalk X' z,
        ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
          (hP : P.IsKFlat)
          (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
          ∃ hsP : IsIso (ε.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P))),
            ∀ i : ℤ,
              (ModuleCat.scalarExtensionHomologyIso (A := A g' z) (D := C z)
                _ L ε (stalkComplex g' z P) hsP i).inv ≫
                (DerivedCategory.homologyFunctor _ i).map
                  (L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
                    (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
                      j.hom.app (DerivedCategory.Q.obj P)) =
              HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
                (comparisonStalkHomologyIso X' z
                  (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
                    i).inv ≫
                (comparisonStalkCohomology X' z i).map
                  (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
