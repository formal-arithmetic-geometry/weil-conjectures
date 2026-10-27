/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.Paper.ComponentDerivedSquareData

/-! # Coefficient-normalized ordinary component edges

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- The edges and the intrinsic slice coherence, before any component square.
Source: HRS (4.1) (blueprint: lem-zl-component-ordinary-edges). -/
structure OrdinaryEdges (Λ : Profinite.CondensedRing.{u}) where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  identity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  composition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))

/-- Construct the normalized component and slice edges, with their slice comparisons.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9
(blueprint: lem-zl-component-ordinary-edges).

Proof: use the actual inverse images adjoint to restriction along the relative
component tests and profinite base change. The component-site theorem and the
left-exact site inverse-image theorem give braided structures and finite exactness.
Their oplax maps are the adjunction mates of the pointwise tensor maps, giving the
two canonical equations in Corner and Slice. Identify absolute tests by the unique
map preserving the base and profinite coordinates. Restricting sheaves along this
identification and taking its adjunction mate defines beta. The right comparison
is pointwise monoidal, so beta is monoidal. Apply mapMon to beta at Λ to define
the coefficient isomorphism; its underlying map is beta at Λ by construction.
For slice identities use the first pullback projection, and for composition the
unique map to the iterated pullback preserving its two projections. Their
restriction isomorphisms have exactly the prescribed section formulas. Take their
mates to define the abelian comparisons. Coordinate compatibility at P × S gives
the coefficient equations. Hence the comparisons are linear on internal modules;
lift with Mod.isoMk and forgetful faithfulness. This constructs SliceIdentity and
SliceComposition including their underlying-map equalities. No scheme square or
coherence between scheme squares is asserted here. The construction also applies
to the empty component space and to the zero ring. -/
theorem component_ordinary_edges (Λ : Profinite.CondensedRing.{u}) :
    Nonempty (OrdinaryEdges Λ) := by sorry

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
