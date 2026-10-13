/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Tensor compatibility of a fixed stalk chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-tensor-stalk-fixed-map-square).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Tensor comparison for the fixed chain map induced by the coordinates c.

Proof: take the total tensor of the K-flat sheaf complexes P and c.P.
The localization tensor map identifies its derived object with E tensor K via
eP and c.e. The stalk tensor isomorphism identifies its stalk with U tensor Q.
The canonical pullback tensor equation in hτ identifies the pullback of this
representative with the tensor of the two termwise pullbacks, using the shared
counit. Compose with tensoring c.t. The represents equation of c and naturality
of τ show that this chain map represents τ followed by tensoring φ.
The pullback-stalk isomorphisms and tensor associativity identify its stalk map
with the inverse scalar-extension tensorator followed by tensoring t. This
identification is fixed on each tensor summand by the canonical module maps.
Exact stalks and derived cohomology supply the target isomorphism to d.N through
this representation and d.represents. The source isomorphism is induced by the
derived isomorphism from P tensor c.P to d.P; its A-tensor-R-B linearity follows
from the model's cohomologyIso_smul equation. The universal derived scalar-extension
counits make the source isomorphism compatible with comparison_eq; localized_eq
transposes the equality to C-linear maps. Naturality of comparison into pullback
for derived isomorphisms yields the displayed square for arbitrary d.
No horizontal comparison is assumed invertible. The construction uses unbounded
K-flat representatives; zero complexes and zero rings cause no exception.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), the tensor-transitivity computation
of Tag 0BYJ, with equation-bc before Tag 0DJ8 and the canonical tensor equation.
(blueprint: lem-pc-tensor-stalk-fixed-map-square). -/
theorem tensorStalkComparison_fixedMap_square
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
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ E.obj) (hP : P.IsKFlat) (z : X') :
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
    let mU := ModuleCat.baseDerivedTensorCohomologyModel R A B (U ⊗ Q) C
    ∀ i : ℤ,
      ∃ (aU : G.obj (mU.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P).cohomology i))
        (bU : (F.obj U ⊗ S.obj c.N).homology i ≅ (S.obj d.N).homology i),
        aU.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq d z i =
          mU.localizedComparison i ≫ HomologicalComplex.homologyMap
            ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i ≫ bU.hom := by sorry

end AlgebraicGeometry
