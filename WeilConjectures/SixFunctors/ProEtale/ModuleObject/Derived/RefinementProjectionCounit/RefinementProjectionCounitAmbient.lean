/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection

/-!
# Proper refinement intertwines ambient condensed projection maps

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, compactification-independence sentence
(blueprint: lem-sf-refinement-projection-counit).

The statement uses the native ordinary unbounded condensed module categories.  The
refinement map is the normalized clopen reindexing map and the projection map is the
counit-defined compactification projection supplied by `exchangeProjectionData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing.RefinementProjectionCounit

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The counit-defined compactification projection map.

Source: the projection paragraph of `def-exchange-projection`
(blueprint: lem-sf-refinement-projection-counit).  The identity base-change edge is
chosen in `exchangeProjectionData`; its `projection` field is the native map
`S_p (δ_j) ∘ π_p` with the specified normalized open tensor comparison.
-/
noncomputable def PF {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : D Λ X) (L : D Λ Y) :
    (F Λ c).obj K ⊗ L ⟶ (F Λ c).obj (K ⊗ (P Λ f).obj L) :=
  (exchangeProjectionData Λ c (𝟙 Y)).projection K L

end AlgebraicGeometry.ProEtale.CondensedRing.RefinementProjectionCounit
