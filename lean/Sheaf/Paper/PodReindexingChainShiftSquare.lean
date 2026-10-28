/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Reindexing square for supplied signed chain shifts

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: new-pod-reindexing-chain-shift-square).
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

/-- The supplied signed shifts satisfy the chain reindexing square.

For each product projection, both routes reindex the source factor from `p`
to `p-a` and carry the scalar `(-1)^(a*r)`.  The `chain_projection` field of
the normalized comparison identifies the two projection maps.  Product
extensionality then gives the displayed equality of chain morphisms.  This is
strictly smaller than the existence theorem because the two shift structures
are fixed as hypotheses.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: new-pod-reindexing-chain-shift-square). -/
theorem chain_shift_reindexing_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (sX : ChainShift l E X s) (sY : ChainShift l E Y s) :
    (∀ (P I : K l E Y s) (a b : ℤ),
      (c.chain (P⟦a⟧) (I⟦b⟧)).hom ≫
        (((podReindexingHom l E X s).map
          ((complexShift l E g s a).inv.app P).op).app
            ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)) ≫
          ((podReindexingHom l E X s).obj
            (op (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧))).map
              ((complexShift l E g s b).hom.app I)) ≫
        (sX.iso ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I) a b).hom =
        (podReindexingComplexFunctor l E g s).map (sY.iso P I a b).hom ≫
          (complexShift l E g s (b-a)).hom.app
            (hom l E Y s P I) ≫ ((c.chain P I).hom)⟦b-a⟧') := by
  sorry

end WeilConjectures.PodReindexingCoherence
