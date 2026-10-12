/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Base change compatibility of the direct-image counit

Source: WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean,
`nonempty_arrowIso_pullback_directImageCounit`
(blueprint: lem-pc-arrow-iso-pullback-counit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a class in `F(T)`, pulling the direct-image counit back along `i_X` gives an arrow
isomorphic to the direct-image counit of the pulled-back module.
Source: ZeroScheme.lean, `nonempty_arrowIso_pullback_directImageCounit`
(blueprint: lem-pc-arrow-iso-pullback-counit).

Proof: (1) Membership in `F(T)` gives `Rf_* L ≅ N[0]` with `N` invertible
(def-pc-f-subfunctor, def-pc-invertible-in-degree-zero), hence `N ≅ f_* L` by zeroth
cohomology. The invertible module `L` is quasi-coherent and flat over `T`, since the curve
is smooth (def-sc-invertible-module, lem-pc-smooth-flat). The base-changed projective
morphism is quasi-compact and separated. Derived flat base change
(lem-pc-rf-base-change-flat-module) applies; since `N` is flat, taking zeroth cohomology
shows that the canonical base-change map `i^* f_* L → f'_* i_X^* L` is an isomorphism.
(2) The pullback-composition isomorphism (lem-pc-module-pullback-identity-composition)
identifies `i_X^* f^*` with `f'^* i^*`. The base-change map is the adjoint of the pulled-back
counit under this identification. The triangle identity
(lem-pc-module-pullback-adjunction) gives a commuting square between the two counits.
Its source edge is the composition isomorphism followed by the pullback of the base-change
isomorphism; its target edge is the identity of `i_X^* L`. Both edges are isomorphisms,
so the square is the required isomorphism in `Arrow`. -/
theorem nonempty_arrowIso_tensorPullback_directImageCounit
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [(X ↘ Spec (.of k)).IsSmoothProjectiveCurve]
    [GeometricallyIntegral (X ↘ Spec (.of k))]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]
    {T T' : Over (Spec (.of k))} (i : T' ⟶ T)
    (ℒ : picardInvertibleDirectImageClasses (X ↘ Spec (.of k)) σ hσ T) :
    let M := (fromSkeleton _).obj ℒ.1.1.val
    let iX := baseChangeMap (X ↘ Spec (.of k)) i
    let fT := pullback.snd (X ↘ Spec (.of k)) T.hom
    let fT' := pullback.snd (X ↘ Spec (.of k)) T'.hom
    let adjT := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction fT)
    let adjT' := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction fT')
    Nonempty (Arrow.mk ((Scheme.Modules.tensorPullback iX).map (adjT.counit.app M)) ≅
      Arrow.mk (adjT'.counit.app ((Scheme.Modules.tensorPullback iX).obj M))) := by
  sorry

end AlgebraicGeometry
