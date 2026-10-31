/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemTensorMateArrows

/-! # The tensor square for the localized clopen arrow

Source: Stacks 0F7B, 0E8I and 0B56; Steps 2--3 of the proper/open
projection-mate calculation (blueprint: lem-pur-system-clopen-alpha-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.SystemTensorMate

/-- Tensor compatibility of alpha, before taking either proper-adjunction mate.

Source: Stacks 0F7B (open base change and clopen lift), 0E8I (open tensor),
0B56 (tensor-pullback comparison); Steps 2--3 of lem-sf-proper-open-projection-mate.
The assertion on the whole varying-coefficient system category is agent-formulated.
(blueprint: lem-pur-system-clopen-alpha-tensor-square).

Proof: form B_C = B ×[F] C, with projections b,q. The lift s=(k,r) is clopen.
The ordinary alpha is open base change beta followed by b_! of the projection
onto s(A) and the canonical open/pullback compositors. The unique restriction
condition defining ordinaryAlpha identifies this composite, and exact localization
identifies alpha with it on the unbounded system categories.
First compare beta with tensor: both sides are extended from the open B_C, so
restrict to it using full faithfulness. The normalized open units cancel, leaving
mu_q and the canonical pullback square on both routes. Next the clopen projection
is (identity,zero) on B_C=s(A) disjoint union its complement. Tensor with P_b P_p Q
commutes with this projector, and the open tensor comparison on s restricts to
identity on s(A), with zero target on the complement. This identity holds on
complexes and commutes with all coefficient transitions. Descend through the
K-flat models and localizations, without evaluation. Finally the comparison for
b_!s_! agrees with delta_k: their open-unit transposes agree, so the open Hom
bijection identifies them. Pasting the beta and projector squares gives the
formula below. The final square factor is oriented P_k P_p → P_r P_i, exactly
as in Operations.square. No right-derived direct image or proper mate is used. -/
theorem system_clopen_alpha_tensor_square
    (K : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ K.p)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : TensorOperations l E)
    {A B C F : Scheme.{u}}
    [A.Over (Spec (.of K.k))] [B.Over (Spec (.of K.k))]
    [C.Over (Spec (.of K.k))] [F.Over (Spec (.of K.k))]
    [IsSeparated (A ↘ Spec (.of K.k))] [LocallyOfFiniteType (A ↘ Spec (.of K.k))]
    [QuasiCompact (A ↘ Spec (.of K.k))]
    [IsSeparated (B ↘ Spec (.of K.k))] [LocallyOfFiniteType (B ↘ Spec (.of K.k))]
    [QuasiCompact (B ↘ Spec (.of K.k))]
    [IsSeparated (C ↘ Spec (.of K.k))] [LocallyOfFiniteType (C ↘ Spec (.of K.k))]
    [QuasiCompact (C ↘ Spec (.of K.k))]
    [IsSeparated (F ↘ Spec (.of K.k))] [LocallyOfFiniteType (F ↘ Spec (.of K.k))]
    [QuasiCompact (F ↘ Spec (.of K.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ F) (i : C ⟶ F)
    [k.IsOver (Spec (.of K.k))] [r.IsOver (Spec (.of K.k))]
    [p.IsOver (Spec (.of K.k))] [i.IsOver (Spec (.of K.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (G : D l E C) (Q : D l E F) :
    (o.P p).map ((o.delta i G Q).hom) ≫
        (o.alpha k r p i h).app ((o.T C).obj (G, (o.P i).obj Q)) ≫
        (o.J k).map ((o.mu r).hom.app (G, (o.P i).obj Q)) =
      (o.mu p).hom.app ((o.J i).obj G, Q) ≫
        (o.T B).map (Prod.mkHom ((o.alpha k r p i h).app G) (𝟙 ((o.P p).obj Q))) ≫
        (o.delta k ((o.P r).obj G) ((o.P p).obj Q)).hom ≫
        (o.J k).map ((o.T A).map
          (Prod.mkHom (𝟙 ((o.P r).obj G)) ((o.square k r p i h).hom.app Q))) := by
  sorry

end WeilConjectures.SystemTensorMate
