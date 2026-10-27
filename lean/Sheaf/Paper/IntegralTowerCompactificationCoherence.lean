/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.Paper.IntegralDirectImageTowerData

import Sheaf.Paper.IntegralModels
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Restrict compactification coherence to integral bounded constructible objects.
Source: blueprint latest direct-image.proof.md paragraph (2), independence sentence.
Proof: the schemes are qcqs and the integral coefficients are admissible. The integral-model
criterion identifies bounded constructible objects with finite-Tor constructible objects,
which lie in the ambient localizing closure. Apply compactification_coherence_cocycle and
whisker its comparisons with this full-subcategory inclusion. Every compactification open
is quasi-compact by QuasiCompact.of_comp, so it defines a boundary compactification.
Transport along these canonical lifts. Their underlying compactifications are unchanged;
the identity, cocycle and dense-refinement normalization equations therefore restrict
componentwise. Empty schemes and equal compactifications require no exception.
(blueprint: lem-sp-integral-tower-constructible-coherence). -/
theorem constructible_compactification_coherence :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∃ φ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₂,
      (∀ c : Compactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) ∧
      ∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f)
        (h₁ : r.obj ⟶ c₁) (h₂ : r.obj ⟶ c₂) (M : Constructible l E X),
        (φ c₁.obj.obj c₂.obj.obj).hom.app M ≫
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₂ M.obj =
        CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₁ M.obj
 := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
