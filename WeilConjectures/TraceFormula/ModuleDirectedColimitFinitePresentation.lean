/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Every module is a directed colimit of finitely presented modules

Every module over a ring is a directed colimit of finitely presented modules.

## References

* Stacks Project, Tag 058G (proof of Lazard's theorem)
-/

@[expose] public section

-- This proof-only module intentionally exports no declarations.
set_option linter.privateModule false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

noncomputable section

private abbrev freeMap (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : (M →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R id

private abbrev PresentationIndex (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :=
  {a : Finset M × Submodule R (M →₀ R) //
    a.2.FG ∧ a.2 ≤ Finsupp.supported R R (a.1 : Set M) ∧ a.2 ≤ (freeMap R M).ker}

private abbrev stageFree {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  Finsupp.supported R R (i.1.1 : Set M)

private abbrev stageRelations {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  i.1.2.comap (stageFree i).subtype

private abbrev stage {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  (stageFree i) ⧸ stageRelations i

end

end Module
