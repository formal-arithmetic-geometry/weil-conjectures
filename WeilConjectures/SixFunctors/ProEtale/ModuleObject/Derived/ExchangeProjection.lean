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

/-- Independence of the specified compact-support exchange from compactification.

The two comparison families are normalized by every common refinement, before
and after the same arbitrary base change.  The last equation therefore compares
exactly the constructed exchange maps, rather than unspecified isomorphisms.

Source: blueprint `def-exchange-projection`, compactification-independence
sentence; repair note, Wei Yang #1412 item 2 (blueprint: def-exchange-projection).

Proof: for a refinement, the open-adjunction transpose of the identity on the
common open defines its canonical morphism.  Restriction to the complementary
closed subscheme is zero by the original-coefficient boundary-vanishing lemma;
joint open/closed detection makes the refinement morphism invertible.  The two
base-change/refinement composites both restrict to the same identity on the
common open.  Open adjunction equates them, and proper direct image together
with mate pasting gives refinement-exchange compatibility.  Choose a common
refinement for each pair.  The refinement identity and composition laws, after
passing to a common further refinement, give independence of choices and
naturality.  Apply the compatibility to both common-refinement arrows and
cancel their invertible images.  This gives the final equality without changing
coefficients or inverting the exchange map.
-/
theorem exchangeProjection_compactification_independent
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) (_hn : 1 ≤ n)
    (_hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFiniteCoefficient ℓ E n)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenIntegralCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFieldCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (S : Scheme.{u}) (_hℓ : ∀ s : S, IsUnit (ℓ : S.residueField s))
    {X Y Y' : Scheme.{u}}
    [X.Over S] [Y.Over S] [Y'.Over S]
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    [LocallyOfFiniteType (Y' ↘ S)] [QuasiCompact (Y' ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver S] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v] :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
      ∃ τ' : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙
            P Λ (pullback.fst f v) ⋙ F Λ (c₁.baseChange v) ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙
            P Λ (pullback.fst f v) ⋙ F Λ (c₂.baseChange v),
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (τ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
            (refinement Λ h₁).app K.obj) ∧
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (τ' c₁ c₂).hom.app K ≫
              (refinement Λ (refinementBaseChange h₂ v)).app
                ((P Λ (pullback.fst f v)).obj K.obj) =
            (refinement Λ (refinementBaseChange h₁ v)).app
              ((P Λ (pullback.fst f v)).obj K.obj)) ∧
        (∀ (c₁ c₂ : Compactification f)
            (K : BoundedConstructible (condensedRingObj Λ X)),
          (P Λ v).map ((τ c₁ c₂).hom.app K) ≫
              (exchangeProjectionData Λ c₂ v).compact.app K.obj =
            (exchangeProjectionData Λ c₁ v).compact.app K.obj ≫
              (τ' c₁ c₂).hom.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
