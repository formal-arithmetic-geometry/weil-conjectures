/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Detection of affine module section vanishing at one stage

Source: Stacks Project, Limits, Tag 01ZR (3), affine part of the first proof;
Algebra, Tags 05N7 (3) and 05LI (1).
(blueprint: lem-pc-affine-section-zero-at-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A section killed at the affine inverse limit is killed at one stage.
Source: Stacks Project, Limits, Tag 01ZR (3), first proof; Algebra, Tag 05LI (1).
(blueprint: lem-pc-affine-section-zero-at-stage).

Proof: the inverse images of U are affine by base change of affine morphisms.
Restrict the ring diagram to the upper tail of j. Pullback pasting and
isLimitBaseChangeCone identify the limit chart with the inverse limit of the
stage charts; the affine Spec/Gamma equivalence identifies its ring with their
filtered colimit. Quasi-coherence identifies pullback sections with scalar
extension of G on the j-th chart. The canonical unit sends y to 1 tensor y.
Apply the zero clause of TensorProduct.directedColimitBaseChangeElementwise to
this tensor to obtain one later stage. The affine pullback comparison is
bijective and therefore reflects zero. Finally uniqueness of left adjoints
intertwines any supplied adjunction unit with the canonical unit by an
isomorphism. Its section components preserve and reflect zero. This includes
empty charts and zero modules and does not require finite presentation. -/
theorem section_affine_open_zero_at_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hG_qc : G.IsQuasicoherent)
    (U : Xi.Opens) (hU : IsAffineOpen U)
    (y : Γ(G, (pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U))
    (adjlim : Scheme.Modules.tensorPullback
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) ⊣
      Scheme.Modules.pushforward
        (baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))))
    (adjstage : ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (hy : (adjlim.unit.app G).val.app
      (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0) :
    ∃ (l : I) (hjl : j ≤ l),
      ((adjstage l hjl).unit.app G).val.app
        (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0 := by
  sorry

end AlgebraicGeometry
