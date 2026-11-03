/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CurrentPurityConventions.Setting.CurrentPurityConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Passing complement-unit invertibility through native Tate coefficients

Source: integral limits and rational filtered colimits in native bottom descent.
(blueprint: lem-pur-native-tate-restriction-unit-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.PurityFiniteSetting

/-- Finite coefficient complement units imply the units for every native Tate coefficient.
Source: blueprint smooth-divisor bottom descent, Steps 3--4; sk-def-sp-tate-twist and
sk-prop-sfb-qlbar-colimit-x.
Proof: forget scalars to abelian pro-etale sheaves, where the canonical native unit
is the abelian open unit up to the scalar pullback comparison. These forgetful functors
are faithful and exact and reflect isomorphisms. For the integers of each finite
extension E, present the root-normalized line as the inverse limit of its finite
quotient twists, using their specified reduction maps. Open restriction preserves
this limit because a weakly etale inverse image is site localization; direct image
preserves it because it is a right adjoint. Naturality says that the actual unit is
the limit of the finite units, so their compatible inverses give its inverse.
For E invert ell in the integral line, using the scalar localization telescope.
For Qbar take the filtered colimit over finite coefficient subextensions, retaining
all specified inclusions. Open inverse image preserves these colimits, and the
quasi-compact quasi-separated open direct image preserves them by the q=0 filtered
colimit theorem. The units are the colimits of the already invertible units by
naturality. The same root-tower and localization arguments apply directly to Z_ell
and Q_ell. In the finite case apply the hypothesis. Reflect invertibility back to
native modules. No derived inverse limit, perfectness, flatness of finite quotients,
or purity isomorphism is required. Empty schemes and empty complements are included:
the finite-unit hypothesis already handles their sections.
(blueprint: lem-pur-native-tate-restriction-unit-coefficients). -/
theorem nativeTateRestrictionUnit_of_finite
    (ell : ℕ) [Fact ell.Prime] {V T : Scheme.{u}} [IsNoetherian T]
    (j : V ⟶ T) [IsOpenImmersion j]
    (hT : IsUnit (ell : Γ(T, ⊤)))
    (hfinite : ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hA : (ell ^ (n + 1) : A) = 0),
      IsIso ((supportPullbackAdjunction
        ((PurityTransport.Coefficient.finite A fin n hA).obj ell) j).unit.app
          ((PurityTransport.Coefficient.finite A fin n hA).firstLine ell T)))
    (c : PurityTransport.Coefficient ell) :
    IsIso ((supportPullbackAdjunction (c.obj ell) j).unit.app (c.firstLine ell T)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
