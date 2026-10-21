/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68; Q70 duplicate handoff
-/
module

public import Sheaf.Paper.SystemTensorMateArrows

import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.ProperOpenProjectionMate

/-!
# Proper/open tensor-mate interchange on varying coefficient systems

Source: Stacks Project, Tag 0F7B (open case), Tag 0E8I and Tag 0B56;
agent-formulated simultaneous-system refinement
(blueprint: lem-pur-system-clopen-tensor-compatibility).

This is equality in the ordinary derived category of the ringed sequence site,
before evaluation or inverse limit. The operations are universal presentations
of the canonical geometric operations; their existence is supplied in the imported
arrows module. Neither the proper/open arrow nor the projection arrow is inverted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.SystemTensorMate

/-- Proper/open tensor-mate interchange for arbitrary unbounded varying-ring systems.

Source: Stacks 0F7B (open case), 0E8I and 0B56; the intrinsic strict-system clause of
lem-sf-proper-open-projection-mate (blueprint: lem-pur-system-clopen-tensor-compatibility).

Proof: (1) Identify the strict quotient-semilinear systems with those in
lem-coef-semilinear-derived-sections, using R=O_E and exponent n+1. Specialize the
system clause of lem-sf-proper-open-projection-mate to A,B,C,F and k,r,p,i. The
square need not be cartesian; the stated quasi-compact open and proper hypotheses
are precisely those needed for its clopen lift.
(2) The ordinary alpha in the arrows module is the open-base-change map followed
by the identity/zero clopen projector, as in lem-cbc-strict-tower-proper-open-calculus.
Its unique restriction characterization fixes the same composite, including the
refinement case. Localizing and taking the proper-adjunction mate therefore gives
exactly gamma, with eta_p, alpha R_r and k_! epsilon_r in that order.
(3) Projection is the transpose of mu followed by counit tensor identity. Delta
is the open-unit-normalized comparison of lem-sf-open-tensor-normalization; its
inverse has exactly that node's adjunct. The final square comparison is induced
by k followed by p equaling r followed by i, with the canonical pullback compositors.
(4) Apply the intrinsic system projection-mate identity to H,Q. Steps (1)--(3)
identify all of its arrows with the displayed composites. This proves equality
before evaluation, for arbitrary unbounded objects, with no Tor or normalization
condition and without inverting gamma or projection. -/
theorem system_clopen_tensor_compatibility
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
    (H : D l E A) (Q : D l E F) :
    (o.delta i ((pushDerived l E r).obj H) Q).hom ≫
        (o.J i).map (o.projection r H ((o.P i).obj Q)) ≫
        (o.gamma k r p i h).app
          ((o.T A).obj (H, (o.P r).obj ((o.P i).obj Q))) =
      (o.T F).map (CategoryTheory.Prod.mkHom ((o.gamma k r p i h).app H) (𝟙 Q)) ≫
        o.projection p ((o.J k).obj H) Q ≫
        (pushDerived l E p).map
          ((o.delta k H ((o.P p).obj Q)).hom ≫
            (o.J k).map ((o.T A).map
              (CategoryTheory.Prod.mkHom (𝟙 H) ((o.square k r p i h).hom.app Q)))) := by
  sorry

end WeilConjectures.SystemTensorMate
