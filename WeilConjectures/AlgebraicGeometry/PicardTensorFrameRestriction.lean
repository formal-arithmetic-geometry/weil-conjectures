/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates
public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized
import WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionEvaluation

/-! # Residue naturality of explicit rank-one tensor coordinates

## References

* Stacks Project, Tags 0096 and 0BF2
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Raw residue restriction evaluates the normalized rank-one coordinate
(Stacks, Tags 0096 and 0BF2). -/
theorem picardTensorFrame_restriction
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (q : (Modules.overEquiv U).functor.obj (K.X 0) ≅ Modules.unit U.toScheme)
    (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U)
    (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU =
      picardResidueLift W w U hwU)
    (f : (Modules.tensorPullback V.ι).obj (Modules.unit W) ⟶
      (Modules.tensorPullback (W.homOfLE hVU)).obj
        ((Modules.overEquiv U).functor.obj (K.X 0))) :
    (ΓSpecIso (W.residueField w)).hom
      (Modules.picardTensorScalarCoordinate (W.fromSpecResidueField w)
        (picardResidueLift W w U hwU) q
        (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV)
          V.ι (W.fromSpecResidueField w) (W.homOfLE hVU)
          (picardResidueLift W w U hwU) (picardResidueLift_comp W w V hwV) hs f)) =
      W.evaluation V w hwV
        (V.topIso.hom (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f)) := by
  rw [picardTensorFrame_restriction_normalized]
  have he := picardResidueLift_appTop_eval W w V hwV
    (V.topIso.hom (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f))
  simpa only [Iso.hom_inv_id_apply] using he

end AlgebraicGeometry.Scheme
