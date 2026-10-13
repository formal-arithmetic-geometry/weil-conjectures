/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Sheaf.AlgebraicGeometry.DerivedStructureEvaluationOne
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The ordinary restricted structure class

Source: Stacks Project, Tags 06Z0 and 079V.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extend the single A-module complex and identify its tilde with the structure single. -/
def openComparisonStructureComplexIso (A : Type u) [CommRing A] :
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat) ≅
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) := by
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let e : K.extend ComplexShape.embeddingDownNat ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A A) 0 0 rfl
  exact ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso e ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
      (ModuleCat.of A A)

/-- Before comparing the two derived functors, the restricted structure class is the
image of the ordinary tilde class of one under the restricted ordinary-to-derived unit.
Source: Stacks Project, Tag 06Z0, the tilde/sections unit, and Tag 079V, the definition
of derived global sections on an ordinary complex.
(blueprint: lem-sc-open-sections-structure-class).

Proof: The extended single complex is identified with the integer single complex by
extendSingleIso. Its homology identification is extendHomologyIso followed by
singleObjHomologySelfIso. Apply tilde and then restriction. The derived single-functor
comparison and sheafOfModulesEquivOverUnit identify this with O_U[0], giving i.
On ordinary degree-zero sections the latter unit isomorphism takes the restricted
structure section one to the section one. Under openComparisonSectionsIso this is
exactly tilde.toOpen of one: the tildeSelf identification, the single-map comparison,
and extendHomologyIso all take the degree-zero class of one to one, and restriction
of the structure sheaf takes one to one. Exact scalar forgetting identifies the same
cycle class through openComparisonOrdinaryIso. Naturality of the ordinary-to-derived
global-sections unit with the complex isomorphism, and naturality of homologyFunctorFactors,
transport this ordinary equality to the displayed derived equality. This calculation
uses neither a comparison equivalence between the two derived section computations nor
an assertion about Hom sets. If U is empty or A is the zero ring, all classes are zero
and the same cycle calculation applies.
-/
theorem openComparison_structure_class (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let T := openComparisonRestriction A U
    let F := openComparisonGlobalCohomology A U
    let O := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let L := K.extend ComplexShape.embeddingDownNat
    let C := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L
    let η₀ : 𝟭 (ModuleCat.{u} A) ⟶ koszulOpenTilde A ⋙ affineOpenSections A U :=
      { app := fun M ↦ tilde.toOpen M U
        naturality := fun _ _ g ↦ (tilde.toOpen_map_app g U).symm }
    let η := (NatTrans.mapHomologicalComplex η₀ (.up ℤ)).app L
    let j : L.homology 0 ≅ ModuleCat.of A A :=
      K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)
    let i : T.mapDerivedCategory.obj (koszulOpenStructure A) ≅ O :=
      T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
        (openComparisonStructureComplexIso A)) ≪≫
      (T.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
          (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U _)
    F.map i.inv (derivedStructureGlobalOne U.toScheme) =
      openComparisonRestrictedUnit A U C
        ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A))) := by sorry

end
end AlgebraicGeometry
