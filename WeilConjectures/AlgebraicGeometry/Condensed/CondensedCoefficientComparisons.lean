/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Canonical derived condensed coefficient comparisons

Source: master ModuleObject/Colimit/TwoColimit.lean, ExtendScalars;
ModuleObjects/ExtendScalars.lean, Compatibilities
(blueprint: def-weil-pbc-condensed-coefficient-comparisons).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

variable (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [instance] condensedCoefficientCompositeExact

end AlgebraicGeometry.ProEtale
