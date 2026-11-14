/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemRestrictionEvaluationForward

/-! # Evaluation of the restriction comparison for ordinary systems

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Evaluation commutes with the inverse restriction comparison for compact support.
Source: Zheng Construction 4.1 and Lemma 5.16; Stacks Tag 0GL6. -/
theorem etaleSystemRestriction_evaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l)
    (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
    (d : rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (C.rings.obj (op n))) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology (a.app (op n)).hom ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c)
    (hd : d.hom = singleRestriction (a.app (op n)) c)
    (N : Derived X C.rings) :
    (t.supportEvaluation B n).iso.inv.app ((restriction X a).obj N) ≫
        (t.evaluationY B n).E.map ((t.restriction a).iso.inv.app N) ≫
        (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).F.obj N) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).restriction.hom.app N) ≫
        d.inv.app ((t.evaluationX C n).E.obj N) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
          ((t.supportEvaluation C n).iso.inv.app N) := by
  let D := Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom
  let e := (t.supportEvaluation C n).iso.hom.app N
  apply (cancel_mono (D.map e)).1
  dsimp [D, e]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simpa using
    (etaleSystemRestriction_evaluation_forward c l t B C a n d hd N)

end AlgebraicGeometry.Etale.SystemProjection
