/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorLocalizedNaturality
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionLinear
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIso

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

private theorem homology_comparison
    {D : Type u} [CommRing D] [HasDerivedCategory.{w} (ModuleCat.{u} D)]
    {M N : CochainComplex (ModuleCat.{u} D) ℤ}
    {U V W : DerivedCategory (ModuleCat.{u} D)}
    (s : U ≅ DerivedCategory.Q.obj M) (k : V ≅ DerivedCategory.Q.obj N)
    (t : M ≅ N) (v : V ⟶ W) (i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).mapIso s ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app M).inv ≫
        (DerivedCategory.homologyFunctor _ i).map
          (s.hom ≫ DerivedCategory.Q.map t.hom ≫ k.inv ≫ v) =
      HomologicalComplex.homologyMap t.hom i ≫
        ((DerivedCategory.homologyFunctor _ i).mapIso k ≪≫
          (DerivedCategory.homologyFunctorFactors _ i).app N).inv ≫
        (DerivedCategory.homologyFunctor _ i).map v := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, s.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun h ↦ h ≫ (DerivedCategory.homologyFunctor _ i).map k.inv ≫
    (DerivedCategory.homologyFunctor _ i).map v)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} D) i).inv.naturality t.hom).symm

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

end AlgebraicGeometry.SingleComplexBaseChange
