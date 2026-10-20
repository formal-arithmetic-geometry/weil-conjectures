/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare

/-! # Degree-zero compatibility of derived base change with the counit mate

Source: `ZeroScheme.lean`, `nonempty_arrowIso_pullback_directImageCounit` docstring,
degree-zero identification; Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-counit-base-change-degree-zero-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Taking degree-zero cohomology of canonical derived base change gives the ordinary
counit mate, when the original direct image is an invertible module in degree zero.
No invertibility of either base-change map is assumed or asserted here.

Source: `ZeroScheme.lean`, `nonempty_arrowIso_pullback_directImageCounit` docstring,
the identification Rf_*M = N[0] and compatibility with adjunction; Stacks, Remark 08HY.
(blueprint: lem-pc-counit-base-change-degree-zero-comparison).

Proof: Compute Rf_*(M[0]) by an injective resolution of M in nonnegative degrees.
Its cohomology in degree q is R^q f_*M, and negative cohomology vanishes. The positive
vanishing hypothesis and truncation identify it canonically with (R^0 f_*M)[0].
The natural rightDerivedZeroIsoSelf identifies R^0 f_*M with f_*M. Since R^0 f_*M is
invertible, it is flat, so the left-derived pullback counit gives the canonical
identification Lg^*Rf_*(M[0]) = (g^*f_*M)[0]. This supplies a. Likewise M is flat,
so Lg'^*(M[0]) = (g'^*M)[0]; the degree-zero injective-resolution comparison for f'
and rightDerivedZeroIsoSelf supply b, without any higher vanishing hypothesis on f'.
The derived adjunction is pinned to the underived adjunction and the same derived
counits. Identify the explicit tensor pullback with Mathlib's pullback by the unique
isomorphism of left adjoints to the same pushforward that respects their adjunctions.
This transports the tensor counit to the ordinary counit; uniqueness of mates also
transports the tensor composition comparison to pullbackComp and pullbackCongr.
Thus taking H^0 commutes with transposition of the derived base-change
map: its transpose becomes the inverse pullback-composition comparison followed by
g'^* of the underived counit. Applying the underived homEquiv gives precisely the
map displayed below. Naturality of the truncation and resolution comparisons gives
the asserted equality a.hom followed by H^0(beta) followed by b.hom. All comparisons
are canonical, so they agree on open overlaps; zero modules handle empty schemes. -/
theorem counitBaseChange_degreeZero_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M]
    (h0 : SheafOfModules.IsInvertible.{u, u, u}
      (((pushforward f).rightDerived 0).obj M))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr sq.w).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    ∃ (a : (pullback g).obj ((pushforward f).obj M) ≅
        H.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)))
      (b : H.obj ((schemeDerivedDirectImage f').obj ((derivedPullback g').obj E)) ≅
        (pushforward f').obj ((pullback g').obj M)),
      (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
        a.hom ≫ H.map (schemeDerivedBaseChangeMap f f' g g' sq.w E) ≫ b.hom := by
  classical
  dsimp only
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
  let N := (pushforward f).obj M
  let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app ((pullback g).obj N)
  let := h0
  have : SheafOfModules.IsInvertible.{u, u, u} N :=
    SheafOfModules.IsInvertible.of_iso.{u, u, u} ((pushforward f).rightDerivedZeroIsoSelf.app M)
  have := isIso_canonicalSinglePullbackMap g N
  have := isIso_canonicalSinglePullbackMap g' M
  have := isIso_canonicalSingleDirectImageMap f M hq
  let a := k.symm ≪≫ H.mapIso ((asIso (canonicalSinglePullbackMap g N)).symm ≪≫
    (derivedPullback g).mapIso (asIso (canonicalSingleDirectImageMap f M)))
  let b := H.mapIso ((schemeDerivedDirectImage f').mapIso
    (asIso (canonicalSinglePullbackMap g' M))) ≪≫
      canonicalDirectImageH0Iso f' ((pullback g').obj M)
  refine ⟨a, b, ?_⟩
  have h := canonicalDegreeZeroMateSquare f g g' f' sq.w M
  dsimp only at h
  apply (cancel_epi (H.map (canonicalSinglePullbackMap g N) ≫ k.hom)).mp
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  simpa only [a, b, H, N, k, E, Functor.id_obj, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_inv, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc] using h

end AlgebraicGeometry.Scheme.Modules
