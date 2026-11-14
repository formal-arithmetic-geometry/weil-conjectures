/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaRepresentative
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaRepresentative

/-! # Common augmentation representatives

Source: Stacks Project, Tags 03P2 and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every global resolution cycle has a common total-complex class with a coefficient cycle.
Source: Stacks Project, Tag 03P2, the separated affine-cover comparison, and Tag 01FD,
the two augmentations of the injective Čech double complex. -/
theorem additiveCech_common_representative
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (s : (additiveCechGlobal I).cycles n) :
    ∃ (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
      (tα tβ : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tα =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) ∧
      (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) ∧
      (additiveCechTotal U I).homologyπ n tα =
        (additiveCechTotal U I).homologyπ n tβ := by
  -- Only beta comparison and the alpha chain-map property are needed in this direction.
  have _hcover := hcover
  obtain ⟨tα, hα⟩ := additiveCech_alpha_representative U I n s
  obtain ⟨z, tβ, hβ, ht⟩ :=
    additiveCech_beta_representative X U hU I n ((additiveCechTotal U I).homologyπ n tα)
  exact ⟨z, tα, tβ, hα, hβ, ht.symm⟩

end AlgebraicGeometry.Scheme.Modules
