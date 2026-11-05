/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Comparing the two integral coefficient presentations

Source: the coefficient conventions of sk-def-sf-setting and det-lem-int-ext-bound;
Mathlib spectralNorm_unique_field_norm_ext and the definition of finite constant models.
(blueprint: lem-integral-coefficient-ext-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
open CategoryTheory.Limits
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (e : Λ ≅ Λ') [IsMonHom e.hom]
end

end AlgebraicGeometry.ProEtale
