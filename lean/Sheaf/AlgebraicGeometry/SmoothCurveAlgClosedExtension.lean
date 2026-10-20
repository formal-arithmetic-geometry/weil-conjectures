/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.Curve.ConstantInvariance
import WeilConjectures.AlgebraicGeometry.CurveCohomologyConnectedReduction

/-! # Constant-coefficient invariance for smooth curves

The curve input to smooth base change, separated from general qcqs invariance so that
smooth base change does not import acyclicity under arbitrary field extensions.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sbc-thm-algebraically-closed-invariance`: Invariance under extension of
algebraically closed fields.

Let `k ⊆ k'` be algebraically closed fields, let `C` be a smooth separated curve over `k` and
let `d ≥ 1` be prime to `char k`. For every `q ≥ 0` the pullback map
`H^q(C_ét, ℤ/d) ⟶ H^q((C_{k'})_ét, ℤ/d)` along the projection `C_{k'} ⟶ C` is bijective.

The proof uses the independent connected-curve invariance theorem, compactification,
and finite-component assembly. It does not use general qcqs coefficient acyclicity.
Source: Stacks Project, Tag 0A5B, and the connected-curve Jacobian argument of
`thm-sc-constant-invariance`. -/
@[stacks 0A5E]
theorem bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] {k' : Type u} [Field k']
    [IsAlgClosed k'] [Algebra k k'] (d : ℕ) (hd : (d : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod d) q) := by
  have : NeZero d := ⟨fun h ↦ hd (by rw [h]; simp)⟩
  apply bijective_curve_cohomologyMap_of_connected f d q
  intro D g _ _
  obtain ⟨c, hc, hsm, hfin, hclosed⟩ :=
    IsConnectedCurve.exists_smooth_properCompactification g
  have : IsConnectedCurve c.g := hc
  have : Smooth c.g := hsm
  obtain ⟨r, hr, hbij, _⟩ :=
    IsConnectedCurve.constant_cohomology_baseChange_compatible (K := k') g c hfin hclosed d hd
  let i := pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  let e := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))
  have he : Function.Bijective (Sheaf.H.map e.hom q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).mapIso e).hom
  have hb : Function.Bijective
      ((Sheaf.H.map e.hom q).comp (Etale.cohomologyMap i (D.constantZMod d) q)) := by
    simpa only [hr q] using hbij q
  refine ⟨fun x y h ↦ hb.1 (congrArg (Sheaf.H.map e.hom q) h), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hb.2 (Sheaf.H.map e.hom q y)
  exact ⟨x, he.1 hx⟩

end AlgebraicGeometry
