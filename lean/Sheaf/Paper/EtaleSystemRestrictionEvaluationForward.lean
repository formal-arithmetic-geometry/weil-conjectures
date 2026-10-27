/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionData

/-! # Forward restriction evaluation cube for ordinary systems

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks Tag 0GL6.

This is the forward cube whose cancellation gives the inverse restriction
comparison in `EtaleSystemRestrictionEvaluation`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The forward compact-support restriction evaluation cube.

Source: Zheng Construction 4.1 and Lemma 5.16; Stacks Tag 0GL6.
Proof: paste the normalized proper and open restriction comparisons, using
sectionwise identity maps and their inverse-image and right-adjoint mates; exact
localization preserves the resulting square. Naturality of the proper and open
comparisons gives the displayed forward cube. This is the forward form before
cancelling the support evaluation isomorphism and replacing the canonical
single-ring restriction by an arbitrary `d` with `hd`.
(blueprint: lem-pur-etale-system-restriction-evaluation-forward)
-/
theorem etaleSystemRestriction_evaluation_forward
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
    ((t.supportEvaluation B n).iso.inv.app ((restriction X a).obj N) ≫
        (t.evaluationY B n).E.map ((t.restriction a).iso.inv.app N) ≫
        (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).F.obj N)) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
        ((t.supportEvaluation C n).iso.hom.app N) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).restriction.hom.app N) ≫
        d.inv.app ((t.evaluationX C n).E.obj N) := by
  sorry

end AlgebraicGeometry.Etale.SystemProjection
