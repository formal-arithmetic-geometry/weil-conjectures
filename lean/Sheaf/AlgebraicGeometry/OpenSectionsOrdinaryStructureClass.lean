/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The ordinary degree-zero structure class

Source: Stacks Project, Tag 06Z0.
(blueprint: lem-sc-open-sections-ordinary-structure-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The restricted ordinary class of one agrees with the tilde/sections unit class.
Source: Stacks Project, Tag 06Z0, the tilde/sections unit, and its restriction to U.
(blueprint: lem-sc-open-sections-ordinary-structure-class).

Proof: Use the extension comparison to identify L with A[0]. The extension homology
isomorphism followed by the single homology isomorphism sends its degree-zero cycle
one to one. The tilde single comparison is identity in degree zero. Under tildeSelf,
tilde.toOpen sends one to the constant structure section one, by toOpen_eq_const and
StructureSheaf.const_one. Restricting the unit sheaf and the over-site equivalence
preserve this section: their degree-zero maps are restriction of the structure ring,
hence preserve one. The restriction/sections isomorphism is restrictAppIso at the top
followed by transport along U = image(top); these are the same section on U. Apply
homology to these degree-zero maps. Naturality of homologyπ gives equality of the
cycle classes. Finally conjugate by the two exact scalar-forgetting homology
isomorphisms in openComparisonOrdinaryIso; their naturality identifies the same
cycles in the additive-group category. All complexes are concentrated in degree zero,
so there are no boundaries. For empty U and the zero ring every section is zero and
the identical calculation holds. No derived unit or comparison equivalence is used.
-/
theorem openComparison_ordinary_structure_class (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) :
    let T := openComparisonRestriction A U
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
    let e₀ : L ≅ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A) :=
      HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of A A) 0 0 rfl
    let e₁ : C ≅ (CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) :=
      ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso e₀ ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
        (ModuleCat.of A A)
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
    let D := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
    let J := (T.mapHomologicalComplex (.up ℤ)).obj C
    let e : J ≅ D :=
      (T.mapHomologicalComplex (.up ℤ)).mapIso e₁ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≪≫
        (CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
            (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U
              (moduleRings (Spec (.of A)).toRingedSpace))
    let ε : ((S.mapHomologicalComplex (.up ℤ)).obj D).homology 0 ≅ ModuleCat.of B B :=
      (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app _) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of B B)
    HomologicalComplex.homologyMap
        ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 (ε.inv (1 : B)) =
      (openComparisonOrdinaryIso A U C).inv
        ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A))) := by sorry

end
end AlgebraicGeometry
