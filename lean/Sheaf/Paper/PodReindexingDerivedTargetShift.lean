/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Target-shift square for normalized reindexing

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: lem-pod-reindexing-derived-target-shift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Reindexing respects the normalized target shift of derived internal Hom.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: lem-pod-reindexing-derived-target-shift).

Proof: represent the source by a complex and resolve the target by a K-injective
complex. Its target shift is again K-injective. Expand `Comparison.derived_model`
at the two pairs. The `RightNormalization` characterization of `homCommShift`
identifies the vertical arrows with unsigned target reindexing on Hom products.
The `chain_projection` field makes these maps commute with sectionwise
reindexing on each factor; product extensionality proves their chain square.
Localize and use naturality of the localization factors. Cancel the comparison
isomorphisms and transport along the representative isomorphisms to obtain the
square for arbitrary M and N. -/
theorem derived_target_shift_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (M N : podReindexingDerived l E Y s) (b : ℤ) :
    c.derived.hom.app (op M, N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (𝟙 (op ((podReindexingDerivedFunctor l E g s).obj M)))
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj M)).commShiftIso b).hom.app
          ((podReindexingDerivedFunctor l E g s).obj N) =
    (podReindexingDerivedFunctor l E g s).map
      (((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) M).commShiftIso b).hom.app N) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
      (c.derived.hom.app (op M, N))⟦b⟧' := by sorry

end WeilConjectures.PodReindexingCoherence
