/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearOpenClosedData

/-! # Coefficient changes for strict localization
Source: Stacks 03CZ, 03DI and 09A5
(blueprint: lem-sp-semilinear-localization-scalar-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.SemilinearSections.OpenClosed

/-- Compatible coefficient maps preserve the four localization operations and arrows.
The exact localization data at both coefficient towers are supplied; this theorem
constructs only their scalar comparisons, without an existence or exactness claim.
Source: Stacks 03CZ, 03DI, 03CY and 09A5; parent proof steps 2, 3 and 7
(blueprint: lem-sp-semilinear-localization-scalar-compatibility).

Proof: on open restriction and closed direct image, use the identity additive
section map. The actions agree by the coefficient-map square and naturality of
the ring adjunction unit. These identifications commute with every horizontal
restriction because the two composites from B_m to D_n agree (induction on the
adjacent coefficient squares). They give the openPull and closedPush comparisons
with their required section equations. Closed inverse image has the same
underlying abelian inverse image with the action restricted along the inverse
image of the coefficient map; this gives an invertible comparison closedPull.
The module adjunction is the abelian adjunction with that action, so its unit
satisfies closedUnit. For open extension use the comparison induced by identity
on every direct-sum summand, then sheafify. The coefficient-comparison composition
law makes these maps commute with system transitions. The summand formula and
uniqueness of sheafification prove that this comparison carries the actual open
counit to the other actual counit, giving openCounit. Transport along the supplied
open adjunctions by uniqueness of left adjoints. Naturality gives comparisons of
functors, and applying them at differentials gives the complex comparisons.
Only restriction of scalars is used: zero rings, empty pieces and non-flat maps
(such as Z/4 to Z/2) cause no exception. -/
theorem semilinearLocalizationScalarCompatibility
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B D : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (σ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    (φ : ∀ n : ℕ, B n ⟶ D n)
    (hφ : ∀ n : ℕ, φ (n + 1) ≫ σ n = τ n ≫ φ n)
    (P : SequenceData i U B τ) (Q : SequenceData i U D σ) :
    Nonempty (ScalarCompatibility i U B D τ σ φ hφ P Q) := by sorry

end WeilConjectures.SemilinearSections.OpenClosed
