/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.Paper.FieldWeilShriekShiftData
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FieldShriekLowerBound

/-! # Weil equivariance of the compact-support shift comparison

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition/lem-zl-composition-weight-bound.proof.md,
first paragraph, the spectral sequence of Weil sheaves
(blueprint: lem-zl-weil-shriek-shift-compatibility).

Both field models use the recorded constructible categories and their fixed pairs.
The shifts and exchange maps are the normalized proper/open constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The canonical shift comparison for compact support is a Weil isomorphism, at
E and at the algebraic closure, for every integer shift. The geometric Frobenius
maps are semilinear, and no separated structure morphism is required.

Source: blueprint main-20261015,
lem-zl-composition-weight-bound.proof.md, first paragraph
(blueprint: lem-zl-weil-shriek-shift-compatibility).

Proof, the two steps of the DAG:
1. lem-zl-field-shriek-lower-bound supplies exact compact support. The pullback
   construction of def-weil-derived-pullback-tensor-hom carries the canonical
   shift comparisons. Signed Roos reindexing fixes their integral form;
   rationalization and common-stage representatives preserve these comparisons.
   Pullback composition and its Frobenius square commute with these shifts.
   Passing to the proper right mate and open left mate gives the exchange shift
   square for the exact proper/open compact-support functor.
2. Expand the induced Weil structure as Ex! followed by Rf!(theta), as in
   lem-fix-weil-operations. Apply that exchange square, then naturality of the
   compact-support shift comparison to theta. The result is exactly the equality
   below, with the pullback shift inserted in each shifted Weil structure.
   Each comparison is invertible, so this equality makes sigma and its inverse
   morphisms in the existing fixed-pair Weil category. -/
theorem weilShriek_shift_compatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (ι : E →ₐ[Padic l] Ω)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c : Compactification f₀.left) :
    (∀ (K : sfWeilComplex D l hl X₀ E) (r : ℤ),
      (fieldWeilShriekExchange D l hl E f₀ c).hom.app (K.carrier⟦r⟧) ≫
          (fieldWeilShriek D l hl E f₀ c).map
            (((sfWeilFrobeniusPullback D l hl X₀ E).commShiftIso r).hom.app K.carrier ≫
              K.str.hom⟦r⟧') ≫
          ((fieldWeilShriek D l hl E f₀ c).commShiftIso r).hom.app K.carrier =
        (sfWeilFrobeniusPullback D l hl Y₀ E).map
            (((fieldWeilShriek D l hl E f₀ c).commShiftIso r).hom.app K.carrier) ≫
          ((sfWeilFrobeniusPullback D l hl Y₀ E).commShiftIso r).hom.app
            ((fieldWeilShriek D l hl E f₀ c).obj K.carrier) ≫
          ((fieldWeilShriekExchange D l hl E f₀ c).hom.app K.carrier ≫
            (fieldWeilShriek D l hl E f₀ c).map K.str.hom)⟦r⟧') ∧
    (∀ (K : sfCommonStageWeilComplex D l hl X₀ Ω) (r : ℤ),
      (zlShriekFrobenius D l hl Ω f₀ c).hom.app (K.carrier⟦r⟧) ≫
          (zlCommonStageShriek D l hl Ω f₀ c).map
            (((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).commShiftIso r).hom.app
              K.carrier ≫ K.str.hom⟦r⟧') ≫
          ((zlCommonStageShriek D l hl Ω f₀ c).commShiftIso r).hom.app K.carrier =
        (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map
            (((zlCommonStageShriek D l hl Ω f₀ c).commShiftIso r).hom.app K.carrier) ≫
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).commShiftIso r).hom.app
            ((zlCommonStageShriek D l hl Ω f₀ c).obj K.carrier) ≫
          ((zlShriekFrobenius D l hl Ω f₀ c).hom.app K.carrier ≫
            (zlCommonStageShriek D l hl Ω f₀ c).map K.str.hom)⟦r⟧') := by
  sorry

end WeilConjectures
