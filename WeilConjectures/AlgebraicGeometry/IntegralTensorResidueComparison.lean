/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-!
# Monoidal first-residue reduction
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Derived reduction of an ordinary tensor is the tensor of the two reductions
over the residue coefficient ring, rather than over the integral coefficient ring. -/
theorem integralTensorResidueComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (M N : DerivedCategory (AdicCompletion.Modules l E S)) :
    Nonempty
      ((AdicCompletion.derivedReduction l E S 0).obj (M ⊗ N) ≅
        (AdicCompletion.derivedReduction l E S 0).obj M ⊗
          (AdicCompletion.derivedReduction l E S 0).obj N) := by
  let φ := AdicCompletion.quotient l E S 0
  let := Mod.extendScalarsMonoidal φ
  exact ⟨asIso (((Mod.extendScalars φ).leftDerivedTensorComparison.app M).app N)⟩

end AlgebraicGeometry.ProEtale
