/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.ModuleStalkExact
import Mathlib.Topology.Sheaves.Abelian

/-! # Transport of the source of the stalk comparison

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-source-transport).
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

/-- Additivity of the module stalk functor, by additivity of abelian-group stalks. -/
instance comparisonStalkAdditive (Y : Scheme.{u}) (y : Y) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive where
  map_add := by
    intro M N a b
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf _).map (a + b).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf _).map (a.val + b.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- Exactness of the module stalk functor, from the shared stalk exactness theorem. -/
instance comparisonStalkHomology (Y : Scheme.{u}) (y : Y) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro T hT
  exact ((RingedSpace.module_stalk_exact Y.toRingedSpace T.f).2.2.2.2
    T.X₃ T.f T.g T.zero).mp hT y

instance comparisonStalkLimits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteLimits (RingedSpace.moduleStalkFunctor Y.toRingedSpace y) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance comparisonStalkColimits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteColimits (RingedSpace.moduleStalkFunctor Y.toRingedSpace y) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The exact stalk functor on derived categories, with the standard module localization. -/
def comparisonDerivedStalk (Y : Scheme.{u}) (y : Y) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapDerivedCategory

/-- Derived stalk cohomology, as a functor on the sheaf derived category. -/
def comparisonStalkCohomology (Y : Scheme.{u}) (y : Y) (i : ℤ) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  comparisonDerivedStalk Y y ⋙ DerivedCategory.homologyFunctor _ i

/-- Identification of the derived stalk cohomology with the homology of the stalk complex. -/
def comparisonStalkHomologyIso (Y : Scheme.{u}) (y : Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (i : ℤ) :
    (comparisonStalkCohomology Y y i).obj (DerivedCategory.Q.obj P) ≅
      (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
        (.up ℤ)).obj P).homology i :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _

/-- Naturality of the identification of derived stalk cohomology. -/
@[reassoc]
theorem comparisonStalkHomologyIso_naturality (Y : Scheme.{u}) (y : Y)
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (a : P ⟶ Q) (i : ℤ) :
    (comparisonStalkCohomology Y y i).map (DerivedCategory.Q.map a) ≫
        (comparisonStalkHomologyIso Y y Q i).hom =
      (comparisonStalkHomologyIso Y y P i).hom ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
            (.up ℤ)).map a) i := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  simp only [comparisonStalkCohomology, comparisonDerivedStalk,
    comparisonStalkHomologyIso, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    Functor.mapDerivedCategoryFactors_hom_naturality, Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality, Category.assoc]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Exact derived restriction of stalk modules to the base stalk ring. -/
def comparisonBaseRestriction (z : X') :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := leftAlgebra f g' z
  (ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapDerivedCategory

/-- The model's input identifies with the derived restriction of the derived stalk. -/
def comparisonModelInputIso (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := leftAlgebra f g' z
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapHomologicalComplex
        (.up ℤ)).obj (stalkComplex g' z P))) ≅
      (comparisonBaseRestriction f g' z).obj
        ((comparisonDerivedStalk X (g' z)).obj (DerivedCategory.Q.obj P)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := leftAlgebra f g' z
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (R f g' z))).app
      (((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapHomologicalComplex
        (.up ℤ)).obj (stalkComplex g' z P)) ≪≫
    ((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapDerivedCategoryFactors
      |>.symm.app (stalkComplex g' z P)) ≪≫
    (comparisonBaseRestriction f g' z).mapIso
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).mapDerivedCategoryFactors
        |>.symm.app P)

/-- The counit-compatible isomorphism between the two derived tensor functors. -/
def comparisonModelDerivedIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    (cohomologyModel f f' g g' sq z P).derived ≅
      (cohomologyModel f f' g g' sq z Q).derived := by
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let M := cohomologyModel f f' g g' sq z P
  let N := cohomologyModel f f' g g' sq z Q
  have := M.universal
  have := N.universal
  exact Functor.leftDerivedNatIso M.derived N.derived M.counit N.counit
    (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)

/-- The canonical B-linear cohomology transport before lifting to the tensor algebra. -/
def comparisonSourceUnderlyingIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
      ((cohomologyModel f f' g g' sq z P).cohomology i) ≅
    (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
      ((cohomologyModel f f' g g' sq z Q).cohomology i) := by
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let M := cohomologyModel f f' g g' sq z P
  let N := cohomologyModel f f' g g' sq z Q
  let b := comparisonModelInputIso f g' z P ≪≫
    (comparisonBaseRestriction f g' z).mapIso
      ((comparisonDerivedStalk X (g' z)).mapIso a) ≪≫
    (comparisonModelInputIso f g' z Q).symm
  exact M.cohomologyIso i ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (M.derived.mapIso b ≪≫ (comparisonModelDerivedIso f f' g g' sq z P Q).app _) ≪≫
    (N.cohomologyIso i).symm

/-- The canonical underlying cohomology transport lifts uniquely to a tensor-algebra
linear isomorphism. No K-flatness or morphism to a target complex is needed.

Proof: apply exact stalks and exact restriction to the derived isomorphism a. The
unique counit-compatible identification of total left derived scalar extensions
then gives comparisonSourceUnderlyingIso. For every element of A, naturality of a
commutes with multiplication; this holds for derived morphisms because multiplication
is a natural transformation on complexes, hence descends through localization.
The equations cohomologyIso_smul identify these multiplication actions with the
A-actions on the model cohomologies. Thus the underlying B-linear isomorphism and
its inverse commute with A. Tensor-product induction gives A-tensor-R-B linearity.
Bundle the two linear maps as inverse module morphisms. Restriction of scalars is
faithful, so the specified underlying homomorphism determines the isomorphism uniquely.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8; More on Algebra,
derived change of rings (Tag 06Y6).
(blueprint: lem-pc-stalk-comparison-source-transport). -/
theorem exists_comparisonSourceIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∃! e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
