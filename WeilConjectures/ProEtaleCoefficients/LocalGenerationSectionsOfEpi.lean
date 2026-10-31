/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.LocalGenerationDefinitions
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Sections from a finite-free local-generation epimorphism

This is the elementary generating-sections part of the local-generation argument.
(blueprint: lem-sfb-local-generation-sections-of-epi)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Extract sections and the corresponding free epimorphism from a finite-free epi.

The Mathlib `GeneratingSections.ofEpiFree` construction supplies both the indexed
sections and the epi of the map determined by them through `freeHomEquiv`.
(blueprint: lem-sfb-local-generation-sections-of-epi)
-/
theorem localGenerationSectionsOfEpi
    {Y : Scheme.{u}} (V : Y.ProEt)
    (B : Type (u + 1)) [CommRing B]
    (P : Type (u + 1)) [AddCommGroup P] [Module B P]
    (n : ℕ)
    (q : SheafOfModules.free (R :=
        ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
          (RingCat.of B)).over V)
        (ULift.{u + 1} (Fin n)) ⟶
      localGenerationRestrictedModule Y V B P) [Epi q] :
    ∃ t : ULift.{u + 1} (Fin n) →
        (localGenerationRestrictedModule Y V B P).sections,
      Epi ((SheafOfModules.freeHomEquiv
        (localGenerationRestrictedModule Y V B P)).symm t) := by
  let σ := SheafOfModules.GeneratingSections.ofEpiFree q
  exact ⟨σ.s, σ.epi⟩

end AlgebraicGeometry.ProEtale
