/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ProEtaleTensorPullbackModels
import all Sheaf.Paper.ProEtaleTensorPullbackModels
import Sheaf.Paper.ProEtaleTensorPullbackDescentData
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import all Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-!
# Canonical tensor pullback on the small pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The object universe of the site is u+1 and its morphism universe is u.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf
  CategoryTheory.tensorPullbackTotal CategoryTheory.tensorPullbackTotalComponent

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem tensorPair_restriction (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : proEtaleRingModules X R) {U V : X.ProEtᵒᵖ} (i : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((proEtaleOrdinaryTensor X R).obj M).obj N).val.map i
        (proEtaleTensorPair X R M N U m n) =
      proEtaleTensorPair X R M N V (M.val.map i m) (N.val.map i n) := by
  exact modelTensorPair_restriction X R M N i m n

private theorem tensor_hom_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N H : proEtaleRingModules X R}
    (a b : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (m : M.val.obj U) (n : N.val.obj U),
      a.val.app U (proEtaleTensorPair X R M N U m n) =
        b.val.app U (proEtaleTensorPair X R M N U m n)) : a = b := by
  exact modelTensor_hom_ext X R a b h

private noncomputable def normalizedAlgebraicLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage f (Type (u + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  modelNormalizedAlgebraicLift f R

private theorem normalizedAlgebraicLift_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (P : proEtaleRingModules Y R)
    {T : Sheaf (ProEt.topology Y) (Type (u + 1))}
    (z : T ⟶ AlgebraicGeometry.ProEtaleTensorComparison.moduleSets P)
    (U : Y.ProEt) (t : T.obj.obj (Opposite.op U)) :
    ((proEtaleSheafInverseImage f (Type (u + 1))).map z ≫
        (normalizedAlgebraicLift f R).moduleUnderlying.inv.app P).hom.app
          (Opposite.op ((proEtaleBaseChange f).obj U))
            (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app
              (Opposite.op U) t) =
      AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f P U (z.hom.app _ t) := by
  exact modelNormalizedAlgebraicLift_unit f P z U t

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

/-- Pullback preserves flat K-flat representatives and has a unique canonical tensor comparison.
Source: Stacks 07A4 and 0G7E (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: flat pullback and the K-flat pullback theorem preserve the representative class.
Resolve both inputs by flat K-flat complexes. On them, compose the inverse of the total
ordinary comparison with the two tensor representative isomorphisms and the exact
pullback factorization. The displayed square is precisely this construction. Tensor
descent extends it naturally to all derived inputs and proves uniqueness. The identity
resolution gives the same formula when the inputs are already flat K-flat. -/
theorem proEtaleCanonicalTensorPullback
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :
    (∀ P : CochainComplex (proEtaleRingModules Y R) ℤ,
      proEtaleFlatRepresentatives Y R P →
        proEtaleFlatRepresentatives X S
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ∧
    ∃! alpha : a.tensor ⋙ proEtaleRingDerivedPullback f R S c ≅
      ((proEtaleRingDerivedPullback f R S c).prod
        (proEtaleRingDerivedPullback f R S c)) ⋙ b.tensor,
      ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
        (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q),
        ∃ (hp' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q)),
          (proEtaleRingDerivedPullback f R S c).map
              (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
            alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            b.tensor.map (Prod.mkHom
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
          (proEtaleRingDerivedPullbackFactors f R S c).hom.app
              (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)) ≫
            (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv ≫
            b.representative.hom.app
              (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  classical
  let A := proEtaleRingModules Y R
  let B := proEtaleRingModules X S
  let L := proEtaleRingModulePullback f R S c
  let F := L.mapHomologicalComplex (.up ℤ)
  let LF := proEtaleRingDerivedPullback f R S c
  let PR := proEtaleFlatRepresentatives Y R
  let PS := proEtaleFlatRepresentatives X S
  let tR := Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  obtain ⟨hF, ⟨ff'⟩, b0, hb0⟩ := proEtaleTensorPullbackDescentData f R S c
  obtain ⟨alpha, ha, hu⟩ := CategoryTheory.tensorComparisonDescent
    (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
    (D := DerivedCategory A) (E := DerivedCategory B)
    DerivedCategory.Q DerivedCategory.Q F LF (proEtaleRingDerivedPullbackFactors f R S c).hom
    PR PS hF ff' tR tS a.tensor b.tensor a.representative b.representative b0.symm
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  have hb (P Q : CochainComplex A ℤ) :
      DerivedCategory.Q.map (b0.symm.hom.app (P, Q)) =
        (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv := by
    exact congrArg DerivedCategory.Q.map (hb0 P Q)
  refine ⟨hF, alpha, ?_, ?_⟩
  · intro P Q hp hq
    refine ⟨hF P hp, hF Q hq, ?_⟩
    have hh := ha P Q hp hq
    simp only [hb] at hh
    dsimp only [tR, Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hh
    exact hh
  · intro alpha' ha'
    apply hu alpha'
    intro P Q hp hq
    obtain ⟨hp', hq', hh⟩ := ha' P Q hp hq
    simp only [hb]
    dsimp only [tR, Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex]
    exact hh



/-- The unique derived comparison specified on every flat K-flat pair, rather than an
arbitrary natural isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleCanonicalTensorComparison
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :=
  Classical.choose (proEtaleCanonicalTensorPullback f R S c a b).2.exists



end AlgebraicGeometry.Scheme
