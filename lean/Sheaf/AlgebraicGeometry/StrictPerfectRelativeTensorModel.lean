/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # A bounded base-ring model on a strict-perfect tensor chart

Source: Stacks Project, Tags 0DJQ and 08CI, the local relative Tor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

/-- A strict-perfect tensor chart admits a bounded K-flat model over the inverse-image
base ring, together with a common quasi-isomorphic complex connecting it to K restricted
on the chart. Source: Stacks Project, Tags 0DJQ, 08CI and 08CG.

Proof: restrict G to the open site of U and totalize its tensor with L. Boundedness
of the two factors gives the sum interval by checking each summand in total degree.
The terms of L are finite-free retracts and therefore flat, so this tensor represents
the restriction of QK, using eK and eL and exact monoidal open restriction.
At every point of U, express the stalk of each G term as a filtered colimit of its
sections over affine neighbourhoods inside the preimage of a fixed affine base open.
These sections are flat by hGflat; filtered colimits preserve flatness. Localization
of the base ring then shows flatness over the base stalk. Tensoring with the finite-free
retractions of L gives finite sums and retracts of these flat stalk modules. Thus the
scalar restriction T of the total complex is termwise flat over the inverse-image base
ring, and boundedness makes T K-flat. Restrict the given derived model isomorphisms
along the base ring map; they identify T with the scalar restriction of K on U.
Represent this derived isomorphism by a roof H with two quasi-isomorphisms, oriented
from H to the two complexes, using the calculus of fractions for quasi-isomorphisms.
Empty U and reversed intervals give the same construction with zero total terms.
No witness is used to define data outside this existential proposition.
(blueprint: lem-pc-strict-perfect-relative-tensor-model). -/
theorem strictPerfect_relativeTensor_model
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L)
    (a b c d : ℤ)
    (hLb : ∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∃ (T H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ),
      (∀ n : ℤ, n < a + c ∨ b + d < n → IsZero (T.X n)) ∧
      CochainComplex.IsKFlat (R := R.over U) T ∧
      ∃ (s : H ⟶ ((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) (t : H ⟶ T),
        QuasiIso s ∧ QuasiIso t := by sorry

end AlgebraicGeometry.Scheme
