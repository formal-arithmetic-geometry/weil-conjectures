/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom

/-!
# Canonical product comparisons on ordinary condensed coefficient categories

Source: `literature/blueprint/latest/blueprint/sec-six-functors/
sk-def-sf-kv-maps/def-sf-kv-maps.md`, clauses (i)--(iv) (blueprint: def-sf-kv-maps).
The older main-20261015 sketch,
order 2511, has the same four words. The current source uses ordinary condensed
coefficients and constructible exceptional adjoints, rather than completed operations.

All functors below are the existing native module-object functors. The relative
Kunneth interface fixes its isomorphism by the explicit inverse word. The exceptional
arrows are adjunction transposes; no exceptional comparison is assumed invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons

open CompactificationReindexing RelativeKunneth

variable {k : Type u} [Field k] (Λ : ScalarSixRing.{u})

/-- The unit for the exceptional identity functor is the transpose of the canonical
support-identity isomorphism, including compactification independence.
Source: unit identifications in (iv) (blueprint: def-sf-kv-maps). -/
def identityExceptional (H : RelativeKunneth.CanonicalCompositionData Λ.X k)
    (X : SepFinType k) (c : Compactification (𝟙 X.obj.left))
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    M ⟶ (exceptional Λ S).obj M :=
  (adjunction Λ S).homEquiv M M
    ⟨((H.comparison (𝟙 X) c (Compactification.ofIsProper (𝟙 X.obj.left))).hom.app
      (localizingObject Λ _ M)) ≫ (CompactSupportComposition.identity Λ.X X.obj.left).hom.app M.obj⟩

/-- The four maps for a fixed per-morphism constructible exceptional datum S.
The coefficient quantifier ranges over every admissible condensed ring: finite A,
O_E, E, and the finite-subextension-valued algebraic closure. The relative theorem
provides the normalized support comparisons, and S provides only the per-morphism
right adjoints with their defining adjunctions. The four maps themselves are computed.
Source: all clauses (i)--(iv) (blueprint: def-sf-kv-maps). -/
def maps (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (S : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left),
      SixOperationsLocalizingAdjunction Λ.X c) :=
  let R := relativeDatum D ell hne
  let H := (finiteFieldParameters D ell hne).coefficients Λ hΛ
  let A := R.product Λ hΛ
  (ku Λ H A,
    fun (G : Geometry D.k) (c : Models G)
      (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
      (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) ↦
      alpha Λ H A G c (S G.f₁ c.f₁) (S G.f₂ c.f₂)
        (S (G.q ≫ G.v) c.relative.total) L₁ L₂,
    fun (G : Geometry D.k)
      (E₁ L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
      (E₂ L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) ↦
      beta Λ G.t₁.hom.left G.t₂.hom.left E₁.obj L₁.obj E₂.obj L₂.obj,
    fun (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
      (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
      (c : Models (verdierGeometry X Y W pX pY sq)) ↦
      let G := verdierGeometry X Y W pX pY sq
      kappa Λ H A X Y W pX pY sq c (S G.f₁ c.f₁) (S G.f₂ c.f₂)
        (S (G.q ≫ G.v) c.relative.total))

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
