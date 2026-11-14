/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSmallGenerator
import WeilConjectures.AlgebraicGeometry.EtaleSmallGeneratorSectionsAux

/-!
# Section-size bound for the affine etale generator

## References

* Stacks Project, Tags 01DO and 03EW
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every section group of the concrete etale generator is small in the scheme universe (Stacks,
Tag 01DO). -/
theorem etaleSmallGenerator_sections_small (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    Small.{u} ((etaleSmallGenerator X).obj.obj U) := by
  obtain ⟨α, f, hf⟩ := etaleSmallGenerator_sections_surjective X U
  exact small_of_surjective hf

end AlgebraicGeometry.Scheme
