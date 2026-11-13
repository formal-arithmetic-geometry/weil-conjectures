/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

import WeilConjectures.AlgebraicGeometry.TensorCoordinateIdentifications
import WeilConjectures.AlgebraicGeometry.TensorPullbackStalkSquare

/-! # Tensor coordinates and the chain-level stalk square

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- Tensor coordinates for the given representative, with a chain-level stalk square. -/
theorem exists_tensorStalk_chain_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (E K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hτ : IsCanonicalPullbackTensorComparison g' τ)
    (c : SingleComplexBaseChange.Coordinates g' K.obj K'.obj φ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ E.obj) (hP : P.IsKFlatTensor) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let G := ModuleCat.extendScalars.{u, u, u} (algebraMap (TensorProduct R A B) C)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let Q := SingleComplexBaseChange.stalkComplex g' z c.P
    let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z c.P).hom ≫ S.map c.t
    ∃ (e : SingleComplexBaseChange.Coordinates g' (E.obj ⊗ K.obj)
        (((derivedPullback g').obj E.obj) ⊗ K'.obj)
        (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ)))
      (σ : U ⊗ Q ≅ SingleComplexBaseChange.stalkComplex g' z e.P)
      (ρ : F.obj U ⊗ S.obj c.N ≅ S.obj e.N),
      e.P = pullbackTensorTotal X P c.P ∧
      e.N = pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) c.N ∧
      F.map σ.hom ≫ (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z e.P).hom ≫
          S.map e.t =
        (Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t) ≫ ρ.hom := by
  classical
  let := pullbackDescentModuleTensor X
  let := pullbackDescentModuleTensor X'
  let := modulePreadditive X
  let := modulePreadditive X'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : (curriedTensor X'.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X'.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  let : ∀ M : X'.Modules, ((curriedTensor X'.Modules).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X'.sheaf M
  obtain ⟨χ, hdegree, hcounit⟩ := hτ.1 P c.P hP c.isKFlat
  obtain ⟨e, e', hflat, hiso, hrep⟩ :=
    exists_tensor_coordinate_identifications g' E.obj K.obj K'.obj φ τ hτ.2 c
      P eP hP χ hcounit
  let d := χ.hom ≫
    HomologicalComplex.mapBifunctorMap (𝟙 _) c.t (curriedTensor _) (.up ℤ)
  let coords : SingleComplexBaseChange.Coordinates g' (E.obj ⊗ K.obj)
      (((derivedPullback g').obj E.obj) ⊗ K'.obj)
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ)) :=
    { P := pullbackTensorTotal X P c.P
      N := pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) c.N
      e := e
      e' := e'
      isKFlat := hflat
      counit_isIso := hiso
      t := d
      represents := hrep }
  obtain ⟨σ, ρ, hsquare⟩ :=
    exists_tensor_pullback_stalk_square f f' g g' sq P c.P c.N c.t χ hdegree z
  exact ⟨coords, σ, ρ, rfl, rfl, hsquare⟩


end AlgebraicGeometry
