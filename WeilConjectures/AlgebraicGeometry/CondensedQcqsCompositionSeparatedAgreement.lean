/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionDefs

/-! # Separated-model agreement of normalized qcqs comparisons

Source: Stacks Tag 0F7J and the qcqs compactification tower construction
(blueprint: lem-zl-qcqs-separated-agreement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The geometric separated-model comparison identifies the normalized qcqs data with
its separated finite-type realization after imposing separatedness on the three bases.
Source: the separated specialization in the proof of lem-zl-condensed-shriek-composition-qcqs
(blueprint: lem-zl-qcqs-separated-agreement).

Proof:
1. Assume the three structure morphisms are separated. Identify D.geometricFiber and
zlGeometricScheme, and their maps, by their common pullback definition. The inclusion of ordinary
bounded constructible objects in the localizing closure supplies K-prime with the same ambient
object. Given normalized comparison data, compare alpha on a compatible tower with the
recorded separated composition: both use the open-adjunction transpose of inverse restriction
and the same proper/open compositors. Their refinement maps have the same transpose, so cancel
common
refinements to identify the maps at every compactification. Both exchanges are the specified
proper counit mate followed by the open exchange and the same refinement. The exact-to-total-
derived pullback comparisons identify their input and output functors; these identifications yield
precisely the required HEq clauses. -/
theorem qcqsSeparatedAgreement
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    ∀ [IsSeparated X₀.hom] [IsSeparated Z₀.hom] [IsSeparated Y₀.hom],
      SeparatedAgreement ℓ D hℓ h₀ g₀ A := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
