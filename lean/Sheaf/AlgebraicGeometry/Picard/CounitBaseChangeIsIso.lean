/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-!
# Degree-zero base change for an invertible direct image

Source: the degree-zero comparison in the proof of lem-pc-arrow-iso-pullback-counit.
(blueprint: lem-pc-counit-base-change-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical degree-zero base-change map is invertible when an invertible module
has invertible zeroth direct image and vanishing positive direct images.

Source: ZeroScheme.lean, the first step of the docstring of
`nonempty_arrowIso_pullback_directImageCounit`; blueprint
lem-pc-arrow-iso-pullback-counit, step 1 (derived relatively flat base change).
(blueprint: lem-pc-counit-base-change-is-iso)

Proof: Work locally on affine opens of S and S', refining by affine opens of S'
whose images lie in the chosen affine of S. Direct image and the comparison commute
with these open restrictions. An invertible module is quasi-coherent and flat over
a flat base morphism. A finite affine cover of the inverse image has affine
intersections, since f is separated. Its bounded Cech complex has flat modules over
the affine base ring as terms; the pulled-back cover has the termwise tensor complex.
The proper morphism is quasi-compact and separated. Relatively flat derived base change
therefore identifies the derived pullback of Rf_* M with Rf'_* g'^* M. The positive
cohomology vanishes by hypothesis, so Rf_* M is its zeroth cohomology in degree zero.
The zeroth cohomology is invertible and hence flat, so its derived pullback is its ordinary
pullback in degree zero. Taking zeroth cohomology of the comparison gives an isomorphism
of ordinary direct images. The comparison is canonical: it is the mate of the pullback
composition isomorphism, hence its degree-zero map is the adjoint of the pulled-back
counit precomposed with that composition isomorphism's inverse. This is exactly the map
in the statement. The same argument applies to the empty base, where both modules are zero,
and requires neither a point nor a nonemptiness assumption. -/
theorem isIso_counitBaseChange_of_invertibleDirectImage
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [LocallyOfFinitePresentation f] [Flat f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M]
    (h0 : SheafOfModules.IsInvertible.{u, u, u}
      (((pushforward f).rightDerived 0).obj M))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr sq.w).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    IsIso ((pullbackPushforwardAdjunction f').homEquiv _ _
      (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
