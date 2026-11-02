/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange

/-! # Canonical intrinsic smooth-purity realization

Source: latest blueprint,
`part-duality-trace-formula/sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/prop-weil-operations.proof.md`,
proof sentences 1 and 4 (blueprint: def-pur-canonical-rational-purity-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.GeneralPurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-! The selected data for one specified Brown restriction.  In particular,
`gamma` is data in this structure, rather than an existential hidden in a
proposition. -/
/-- The counit-compatible comparison for the specified Brown restriction.
Source: proof Step 3 of `sk-thm-purity-transport`; blueprint:
`def-pur-normalized-brown-purity`. -/
structure SelectedGamma (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (a : GeneralPurityTransport.AdjunctionFamily ell k)
    (c : Coefficient ell) (s : GeneralPurityTransport.SmoothDatum k)
    (hL : ∀ K, localizing ell c s.X.left K → localizing ell c s.Y.left
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).obj K))
    (G : (localizing ell c s.Y.left).FullSubcategory ⥤
      (localizing ell c s.X.left).FullSubcategory)
    (b : (localizing ell c s.Y.left).lift
      ((localizing ell c s.X.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification)
      (fun K ↦ hL K.obj K.property) ⊣ G) where
  hG : ∀ K : c.ctf ell s.Y.left,
      property ell c s.X.left (G.obj ((inclusion ell c s.Y.left).obj K)).obj
  bctf : support ell c s.compactification (a c s).support_closed ⊣ exceptional ell c G hG
  gamma : source ell c s.map s.dim (a c s).source_closed ≅ exceptional ell c G hG
  compatible : CounitCompatible (a c s).adjunction bctf gamma

end AlgebraicGeometry.ProEtale.PurityTransport
