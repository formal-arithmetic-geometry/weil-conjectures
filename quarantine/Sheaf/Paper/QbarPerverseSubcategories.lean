/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.QbarPerverseSupportCondition

/-! # Perverse classes in the intrinsic common-stage coefficient category

Source: blueprint def-per-perverse-subcategories, all displayed formulas
(blueprint: def-per-perverse-subcategories).
The finite-coefficient and earlier PBC definitions remain available by public import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The support condition after shift by n.
Source: blueprint nonpositive-class formula (blueprint: def-per-perverse-subcategories). -/
def QbarPerverseLE (n : ℤ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  QbarSupportCondition l X Ω (K⟦n⟧)

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]

/-- The cosupport condition after shift by n.
Source: blueprint nonnegative-class formula (blueprint: def-per-perverse-subcategories). -/
def QbarPerverseGE (n : ℤ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  QbarCosupportCondition l X Ω k hl (K⟦n⟧)

/-- The perverse heart candidate is the intersection of the zero classes.
Source: blueprint heart formula (blueprint: def-per-perverse-subcategories). -/
def QbarPerverseHeart :
    ObjectProperty (generalAlgebraicallyClosedConstructibleCategory l Ω X) :=
  QbarPerverseLE l X Ω 0 ⊓ QbarPerverseGE l X Ω k hl 0

end WeilConjectures
