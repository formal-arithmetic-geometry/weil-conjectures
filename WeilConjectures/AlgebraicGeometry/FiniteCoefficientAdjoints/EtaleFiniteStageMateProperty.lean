/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData

/-! # The ordinary etale finite-stage mate property

Source: ordinary etale reduction-exceptional argument and the parent mate proof.
(blueprint: def-pur-etale-finite-stage-mate-property).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

end AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- The fixed counit transpose is invertible on every constructible finite-Tor input.
This is a proposition about the existing operations, not a choice of comparison data.
Source: ordinary etale coefficient-change paragraph of reduction-exceptional
(blueprint: def-pur-etale-finite-stage-mate-property). -/
def EtaleFiniteStageMateProperty
    {l : ℕ} [Fact l.Prime]
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {s t : Stage l E} (a : Arrow s t) (f : X ⟶ Y) : Prop :=
  ∀ (c : Compactification f) (L : Etale.DerivedCategoryModule s.ring Y),
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} s.ring) Y L →
    IsIso ((etaleAdjunction t.ring c).homEquiv _ _
      (Etale.ExceptionalCoefficients.comparisonInverse a.ringMap c
          ((etaleUpper s.ring c).obj L) ≫
        (Etale.scalarExtension a.ringMap Y).map
          ((etaleAdjunction s.ring c).counit.app L)))

end AlgebraicGeometry.FiniteCoefficientAdjoints
