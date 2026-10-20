/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Length of a finite marking at a curve point

Source: Temkin, *Stable modification of relative curves*, §1.2 and Appendix B,
marked exceptional trees (blueprint: def-trf-local-marking-length).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Dimension of the marking's local factor at `x`, or zero if the marking misses `x`.
The sum has at most one term because the marking is a closed immersion. Scalars on that
actual stalk come from the structure map, through `Orgogozo.localScalar`. For a finite
marking its stalk is the local Artinian factor of its finite coordinate algebra, rather
than its scheme-theoretic fibre in the curve. Source: Temkin §1.2 and Appendix B, p. 58
(blueprint: def-trf-local-marking-length). -/
def MultipointedCurve.localMarkingLength {k : Type u} [Field k]
    (P : MultipointedCurve (Spec (.of k))) (x : P.X) : ℕ :=
  ∑ᶠ d : {d : P.D // P.i d = x},
    @Module.finrank k (P.D.presheaf.stalk d.val) _ _
      (Module.compHom (P.D.presheaf.stalk d.val) (Orgogozo.localScalar P.d d.val))

end AlgebraicGeometry
