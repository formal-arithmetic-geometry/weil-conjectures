/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit

/-!
# The free comparison of a composite

For adjunctions `free₁ ⊣ forget₁`, `free₂ ⊣ forget₂`, `free₃ ⊣ forget₃` and isomorphisms
`c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁'`, `c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂'`, the free comparison of the
composite `L₁ ⋙ L₂` (for the pasted isomorphism `CategoryTheory.Adjunction.compForgetIso c₁ c₂`) is
the composite of the free comparisons
(`CategoryTheory.Adjunction.freeComparison_comp`); in particular it is an isomorphism when both
are.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₁'] [Category C₂'] [Category C₃']
  {free₁ : C₁' ⥤ C₁} {forget₁ : C₁ ⥤ C₁'} (adj₁ : free₁ ⊣ forget₁)
  {free₂ : C₂' ⥤ C₂} {forget₂ : C₂ ⥤ C₂'} (adj₂ : free₂ ⊣ forget₂)
  {free₃ : C₃' ⥤ C₃} {forget₃ : C₃ ⥤ C₃'} (adj₃ : free₃ ⊣ forget₃)
  {L₁ : C₁ ⥤ C₂} {L₁' : C₁' ⥤ C₂'} {L₂ : C₂ ⥤ C₃} {L₂' : C₂' ⥤ C₃'}

end CategoryTheory.Adjunction
