/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupGlobalTensorPullback
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Adjunction transpose polygon for the global cup

Source: Stacks, Tag 0FP3, specialized to the map to (pt, Γ(X,O_X)).
(blueprint: lem-sc-module-cup-adjunction-polygon)
This is the adjunction calculation for a chain pairing with K-injective
codomain. The argument passing to an arbitrary codomain is in the importing
compatibility module, by naturality and cancellation of a resolution.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})

-- Share the tensor instances with the pullback comparison theorem.
attribute [local instance 2000] globalPullbackCommRing globalPullbackMonoidal
  globalPullbackSymmetric globalPullbackColimits globalPullbackPreadditive
  globalPullbackClosed

set_option maxHeartbeats 2000000 in
-- Comparing tensor coproduct components unfolds the induced monoidal structures.
/-- Ordinary evaluation commutes with total tensor on cochains.
Source: Stacks, Tag 0FP3, using the naive cup of Tag 0FKU.
(blueprint: lem-sc-module-cup-cochain-counit-tensor)
Proof: in degree n precompose with each tensor summand (i,j), i+j=n. Since P is
an additive left adjoint, it preserves the coproduct used for the total tensor.
The oplax comparison sends that summand to the tensor of its images under P.
The induced counit has components adj.counit at each degree. Naturality of this
counit moves the summand inclusion past evaluation. The resulting equality is
hOrdinary at K.X i and L.X j, after converting the inverse tensor constraint
using its inverse laws. Coproduct extensionality gives equality in degree n;
HomologicalComplex.ext gives equality of the chain maps. Empty summands and
negative degrees use the same coproduct argument, with no boundedness assumption. -/
theorem moduleCup_cochain_counit_tensor
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (hOrdinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      Functor.LaxMonoidal.μ P
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
        P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
          adj.counit.app M ⊗ₘ adj.counit.app N)
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
    F.map (moduleCup_naiveMap X K L) ≫
        (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app (K ⊗ L) =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
        (ComplexShape.up ℤ) P).app (T.obj K)).app (T.obj L) ≫
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K ⊗ₘ
          (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app L)  := by
  dsimp only
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
  let e := adj.mapHomologicalComplex (ComplexShape.up ℤ)
  let z := P.mapCochainComplexμIso (T.obj K) (T.obj L)
  change F.map (moduleCup_naiveMap X K L) ≫ e.counit.app (K ⊗ L) =
    z.inv ≫ (e.counit.app K ⊗ₘ e.counit.app L)
  apply (cancel_epi z.hom).1
  rw [z.hom_inv_id_assoc]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, ← Category.assoc,
    Functor.ιTensorObj_mapCochainComplexμIso_hom_f]
  simp only [Category.assoc]
  change Functor.LaxMonoidal.μ P
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (K.X i))
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (L.X j)) ≫
    P.map (HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n hij) ≫
    P.map (moduleCup_naiveMapComponent X K L n) ≫
    adj.counit.app ((K ⊗ L).X n) = _
  rw [← P.map_comp_assoc]
  change _ ≫ P.map (HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n hij ≫
    moduleCup_naiveMapComponent X K L n) ≫ adj.counit.app ((K ⊗ L).X n) = _
  rw [show HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n hij ≫
      moduleCup_naiveMapComponent X K L n =
    moduleCup_sectionTensorMap X (K.X i) (L.X j) ≫
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (HomologicalComplex.ιTensorObj K L i j n hij) from
    HomologicalComplex.ι_mapBifunctorDesc _ i j hij]
  rw [P.map_comp]
  have hn := adj.counit.naturality (HomologicalComplex.ιTensorObj K L i j n hij)
  simp only [Functor.comp_map, Functor.id_map] at hn
  erw [Category.assoc, hn]
  erw [reassoc_of% (hOrdinary (K.X i) (L.X j))]
  change _ = HomologicalComplex.ιTensorObj (F.obj (T.obj K)) (F.obj (T.obj L))
    i j n hij ≫ (HomologicalComplex.mapBifunctorMap (e.counit.app K)
      (e.counit.app L) (curriedTensor _) (ComplexShape.up ℤ)).f n
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
