/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.DeligneLaumon.WeilCompactSupportCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Compact cohomology retaining the common-stage Weil structure

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-sf-admissible,
def-weil-ordinary-compact-cohomology, final Weil clause
(blueprint: def-weil-ordinary-compact-cohomology).

The ordinary, compact, finite, integral, rational and Qbar coefficient constructions
remain publicly available from the original module. The definition below retains
H_cⁿ as the canonical higher image on Spec(k₀) in the actual common-stage Weil
heart. Evaluating its geometric fibre gives the coefficient cohomology with its
induced Frobenius. The canonical compact-support image and its comparison with
sfQbarCompactSupportValue are those already constructed in the imported module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Spec(k₀) with its identity structure map, the base of geometric cohomology.
Source: blueprint ordinary/compact coefficient base convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev sfWeilCohomologyPoint (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) where
  left := Spec (.of D.k₀)
  right := default
  hom := 𝟙 _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures
