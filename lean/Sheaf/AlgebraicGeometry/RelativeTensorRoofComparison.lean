/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Derived comparison for the relative tensor complexes

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
  Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

/-- The two fixed base-ring complexes are isomorphic after localization.
Source: Stacks Project, Tags 0DJQ and 06YH (local K-flat tensor computation).

Proof: finite-free retracts are flat, so the bounded strictly perfect L is K-flat.
Apply exact monoidal open restriction to eK, and identify the first factor with L
using eL. The K-flat comparison identifies this tensor with the ordinary total
of L and the restriction of G. Restriction of scalars is exact, so it preserves
quasi-isomorphisms and induces a functor on derived categories. Apply that functor
to the preceding isomorphism. Open restriction commutes with scalar restriction
sectionwise; its comparison with the localization functor identifies the first
object with the displayed scalar-restricted K and the second with the explicit
strictPerfectRelativeTensorComplex. This works also for the empty open. The
standard localization of the base-ring category is used, since the hypotheses
only choose localizations for structure-ring modules. This statement concerns
only the derived tensor computation; it does not assert or choose a roof.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof-comparison). -/
theorem strictPerfect_relativeTensor_roof_comparison
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
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (A.over U)) :=
      HasDerivedCategory.standard _
    Nonempty
      (DerivedCategory.Q.obj
        (((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((SheafOfModules.restrictScalars
            ((sheafCompose (Opens.grothendieckTopology X)
              (forget₂ CommRingCat.{u} RingCat.{u})).map
                (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≅
        DerivedCategory.Q.obj (strictPerfectRelativeTensorComplex f U L G)) := by sorry

end AlgebraicGeometry.Scheme
