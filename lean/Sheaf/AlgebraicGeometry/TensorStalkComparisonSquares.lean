/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Ring coordinates for tensor stalk comparisons

Source: Stacks Project, perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-stalk-comparison-squares).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false

namespace AlgebraicGeometry

/-- Simultaneous ring coordinates for the original and tensor comparison maps.
No invertibility of a comparison is asserted.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation using Tag 0BYJ.
Proof: choose K-flat representatives of E and K and a K-injective representative
of K'. Lift phi through the derived counit. Exact stalks give complexes U,Q,N
and the chain map t. The stalk K-flat criterion proves the acyclicity assertions.
Transport the cartesian square to the chosen pullback and apply
lem-pc-pullback-stalk-tensor-flat to the actual stalk algebra maps, so C is flat.
The stalk tensor and pullback identifications, together with
comparison_eq and localized_eq of the cohomology models, give the first square.
Their naturality and tensor associativity give the second square. The represents
identities identify the derived map with phi and its tensor. Coordinate
invariance supplies the vertical isomorphisms for arbitrary c,d. The defining
K-flat equation of hτ, with the shared pullback counit, identifies the tensor
map with the inverse termwise scalar-extension tensorator followed by tensoring t.
Thus the second square follows from a specified equation; it does not assume
compatibility of an arbitrary monoidal structure with the shared counit.
This computation uses arbitrary unbounded K-flat representatives and also
applies to zero complexes and the empty scheme.
(blueprint: lem-pc-tensor-stalk-comparison-squares). -/
theorem exists_tensorStalkComparison_squares
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
    (d : SingleComplexBaseChange.Coordinates g' (E.obj ⊗ K.obj)
      (((derivedPullback g').obj E.obj) ⊗ K'.obj)
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ))) (z : X') :
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
    Module.Flat (TensorProduct R A B) C ∧
    ∃ (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : CochainComplex (ModuleCat.{u} C) ℤ)
      (_ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
      (_ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
      (t : F.obj Q ⟶ N)
      (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : ModuleCat.BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C),
      ∀ i : ℤ,
      ∃ (a : G.obj (m.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z c.P).cohomology i))
        (b : N.homology i ≅ (S.obj c.N).homology i)
        (aU : G.obj (mU.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P).cohomology i))
        (bU : (F.obj U ⊗ N).homology i ≅ (S.obj d.N).homology i),
        a.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq c z i =
          m.localizedComparison i ≫ HomologicalComplex.homologyMap t i ≫ b.hom ∧
        aU.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq d z i =
          mU.localizedComparison i ≫ HomologicalComplex.homologyMap
            ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i ≫ bU.hom := by sorry

end AlgebraicGeometry
