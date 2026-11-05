/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison

/-! # The canonical derived finite coefficient tensor comparison

This construction is the comparison already used by the two-colimit cocone, placed
below that cocone so coefficient complex presentations can state its naturality.
The functor and Hom-equivalence names cache the derived constructions, avoiding
repeated elaboration of their resolution and localization data.
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
