/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingDerivedSourceShiftDescent
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingDerivedSourceShiftModel

/-! # Source-shift square for normalized reindexing

We show that the derived internal Hom comparison of reindexing along an isomorphism respects
the signed shift in the source variable (`derived_source_shift_square`).

## Implementation details

On representatives (source a complex, target K-injective) both routes reindex each
Hom-product factor by the source shift and multiply degree `r` by `(-1)^(a*r)`, while
`chain_projection` identifies the unshifted factors; naturality gives the general case.

## References

* Stacks Project, Tag 0A8X
* Stacks Project, Tag 08JA
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

/-- Reindexing respects the signed source shift of derived internal Hom. -/
theorem derived_source_shift_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (M N : podReindexingDerived l E Y s) (a : ℤ) :
    c.derived.hom.app (op (M⟦a⟧), N) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
          (𝟙 ((podReindexingDerivedFunctor l E g s).obj N))) ≫
      (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj M) a).inv.app
          ((podReindexingDerivedFunctor l E g s).obj N) =
    (podReindexingDerivedFunctor l E g s).map
      ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) M a).inv.app N) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
      (c.derived.hom.app (op M, N))⟦-a⟧' := by
  exact derived_source_shift_descent l E g s SX SY TX TY c
    (derived_source_shift_model l E g s SX SY TX TY c)
    M N a

end WeilConjectures.PodReindexingCoherence
