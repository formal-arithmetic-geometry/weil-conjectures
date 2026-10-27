/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module
public import Sheaf.Paper.ZlImmersionWeilLocalData
public import Sheaf.Paper.WeilIndSheafCategory
/-! # Assembly of the open extension clause
(blueprint: lem-zl-open-extension-assembly). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  {X₀ U₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
/-- Given the normalized open action, its exact operation, Weil unit, and empty-fibre
comparison, assemble the complete open-extension clause. This strictly owns the
record assembly and local field checks of the parent; it does not construct the
immersion restriction package or choose any coefficient-stage action.
Source: latest blueprint, Part 2 extension-by-zero sentence.
(blueprint: lem-zl-open-extension-assembly).
Proof: apply openExtension_tExact and openWeilUnitAndEmptyFibre, then use
the fixed-pair heart/cohomology theorem for the exact operation. Transport the unit along the
restriction comparison equality. The inside stalk equation follows by inverting
the restriction stalk equation and naturality of the inverse unit; outside stalks
follow from geometric disjointness and the canonical scalar/homology comparison. Assemble the
fields using the recorded canonical maps and residue-degree equalities. -/
theorem zlOpenExtensionAssembly
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (dX : ZlFrobeniusComparison D c X₀) (dU : ZlFrobeniusComparison D c U₀)
    (FX : ZlWeilLocalOperators D c X₀) (FU : ZlWeilLocalOperators D c U₀)
    (Rj : ZlImmersionPullback D c j₀ dX dU FX FU)
    (hRj : Rj.equivariance = zlFrobeniusSquare D c.l c.different c.Qbar j₀) :
    Nonempty (ZlOpenExtension D c j₀ dX dU FX FU) := by sorry
end WeilConjectures
