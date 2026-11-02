/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible

/-!
# Exchange and projection transformations

This module records the three canonical transformations in the statement of
`def-exchange-projection`.  They are the native ordinary derived module
operations: the direct-image mate, the compactification exchange, and the
counit projection morphism.  The compactification and the base-change map are
explicit inputs, so no existence or arbitrary choice is hidden in the
construction.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/`
`sec-brown-representability-for-all-coefficient-rings/sk-prop-sf-existence/`
`def-exchange-projection.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical exchange and projection data for a supplied compactification.

The first component is the mate of the pullback-composition comparison
`Lf'^* Lg^* ≅ Lg'^* Lf^*`.  The second is the proper exchange followed by the
canonical open base-change comparison.  The third is the counit-defined
projection morphism for the compactification.  The two naturality equations
are included in the structure so that the returned projection family is a
natural transformation in both variables.

Source: blueprint `def-exchange-projection`, direct-image exchange,
compact-support exchange, and projection paragraphs
(blueprint: def-exchange-projection).
-/
structure ExchangeProjectionData {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) where
  direct : R Λ f ⋙ P Λ v ⟶ P Λ (pullback.fst f v) ⋙ R Λ (pullback.snd f v)
  compact : F Λ c ⋙ P Λ v ⟶
    P Λ (pullback.fst f v) ⋙ F Λ (c.baseChange v)
  projection : ∀ (K : D Λ X) (L : D Λ Y),
    (F Λ c).obj K ⊗ L ⟶ (F Λ c).obj (K ⊗ (P Λ f).obj L)
  projection_natural_left : ∀ {K K' : D Λ X} (φ : K ⟶ K') (L : D Λ Y),
    (F Λ c).map φ ▷ L ≫ projection K' L =
      projection K L ≫ (F Λ c).map (φ ▷ (P Λ f).obj L)
  projection_natural_right : ∀ (K : D Λ X) {L L' : D Λ Y} (ψ : L ⟶ L'),
    (F Λ c).obj K ◁ ψ ≫ projection K L' =
      projection K L ≫ (F Λ c).map (K ◁ (P Λ f).map ψ)

/-- The canonical exchange and projection data.

All three maps are the native constructions in
`CompactificationReindexing` and `ProjectionFormulaBase`; in particular the
compact-support map is computed from the displayed compactification and its
base change, and the projection is computed from the proper counit mate and
open projection comparison.

Source: blueprint `def-exchange-projection` (blueprint: def-exchange-projection).
-/
noncomputable def exchangeProjectionData {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) : ExchangeProjectionData Λ c v where
  direct := baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq
  compact := exchange Λ c v
  projection := fun K L ↦ pf Λ c K L
  projection_natural_left := by
    intro K K' φ L
    simpa only [pf] using
      (exceptionalProjectionMorphismOfCompactification_natural_left Λ c φ L)
  projection_natural_right := by
    intro K L L' ψ
    simpa only [pf] using
      (exceptionalProjectionMorphismOfCompactification_natural_right Λ c K ψ)

end AlgebraicGeometry.ProEtale.CondensedRing
