/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Left adjoints between preadditive categories preserve binary biproducts

A functor between preadditive categories which is a left adjoint preserves binary
coproducts, hence binary biproducts
(`CategoryTheory.Functor.preservesBinaryBiproducts_of_isLeftAdjoint`); if moreover its
source has binary biproducts, it is additive
(`CategoryTheory.Functor.additive_of_isLeftAdjoint`), hence preserves all finite
biproducts. This complements `CategoryTheory.Adjunction.left_adjoint_additive`, which
instead assumes that the right adjoint is additive.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D) [F.IsLeftAdjoint]

/-- A left adjoint between preadditive categories preserves binary biproducts: it preserves
binary coproducts, and in a preadditive category the binary coproduct is the binary
biproduct. -/
lemma Functor.preservesBinaryBiproducts_of_isLeftAdjoint : PreservesBinaryBiproducts F :=
  have : PreservesColimitsOfSize.{0, 0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  preservesBinaryBiproducts_of_preservesBinaryCoproducts F

/-- A left adjoint between preadditive categories whose source has binary biproducts is
additive. Compare `CategoryTheory.Adjunction.left_adjoint_additive`, which instead assumes
that the right adjoint is additive. -/
lemma Functor.additive_of_isLeftAdjoint [HasBinaryBiproducts C] : F.Additive :=
  have := F.preservesBinaryBiproducts_of_isLeftAdjoint
  F.additive_of_preservesBinaryBiproducts

end CategoryTheory
