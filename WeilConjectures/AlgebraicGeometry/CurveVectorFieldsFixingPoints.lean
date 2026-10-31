/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Vector fields preserving point ideals

Source: Stacks Project, curves.tex, section-vector-fields, introduction preceding Tag 0E67
(blueprint: def-sfb-curve-vector-fields-fixing-points).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Apply the sheaf derivation corresponding to a morphism out of relative differentials.
Source: Stacks Project, morphisms.tex, Tag 01UM, universal property, and curves.tex, Tag 0E67
(blueprint: def-sfb-curve-vector-fields-fixing-points). -/
def curveVectorFieldApply {X S : Scheme.{u}} (f : X ⟶ S)
    (D : f.relativeDifferentials ⟶ Scheme.Modules.unit X) (U : X.Opens) (a : Γ(X, U)) :
    Γ(X, U) :=
  D.val.app (op U) (f.relativeDifferentialsDerivation.d (X := op U) a)

/-- Evaluate the derivation represented by a differential-sheaf morphism on a local function
and then at a point. This is the composite of the existing additive evaluation maps.
Source: Stacks Project, curves.tex, section-vector-fields
(blueprint: def-sfb-curve-vector-fields-fixing-points). -/
def curveVectorFieldEvaluation {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (x : X) (hx : x ∈ U) (a : Γ(X, U)) :
    (f.relativeDifferentials ⟶ Scheme.Modules.unit X) →+ X.residueField x :=
  (X.evaluation U x hx).hom.toAddMonoidHom.comp
    ((LinearMap.evalAddMonoidHom
      (M₂ := (Scheme.Modules.unit X).val.obj (op U))
      (f.relativeDifferentialsDerivation.d (X := op U) a)).comp
      (ModuleCat.homAddEquiv.toAddMonoidHom.comp
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.evaluation _ (op U)).mapAddHom)))

/-- Relative derivations preserving the ideal sheaf of each point of `E`, as an additive
subgroup of `Hom(Ω¹, O)`. On each neighbourhood, a function is in the point ideal precisely
when its residue is zero; intersect the kernels of its derivative evaluations. The universal
property `relativeDifferentialsHomEquiv` identifies these morphisms with sheaf derivations.
Source: Stacks Project, curves.tex, section-vector-fields, definition of fixes
(blueprint: def-sfb-curve-vector-fields-fixing-points). -/
def curveVectorFieldsFixingPoints {X S : Scheme.{u}} (f : X ⟶ S) (E : Set X) :
    AddSubgroup (f.relativeDifferentials ⟶ Scheme.Modules.unit X) :=
  ⨅ (x : E) (U : X.Opens) (hx : x.val ∈ U)
    (a : RingHom.ker (X.evaluation U x.val hx).hom),
      (curveVectorFieldEvaluation f U x.val hx a.val).ker

end AlgebraicGeometry
