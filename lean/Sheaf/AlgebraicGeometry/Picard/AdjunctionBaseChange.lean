/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Compatibility of the Picard adjunction morphism with base change

Source: `WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean`,
`nonempty_arrowIso_pullback_directImageCounit`, lines 143–175
(blueprint: lem-pc-zero-scheme-adjunction-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The pullback of the adjunction arrow of a class in `F(T)` is isomorphic to the adjunction
arrow of its pulled-back module, for any morphism of base schemes.
Source: `WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean`, lines 143–175
(blueprint: lem-pc-zero-scheme-adjunction-base-change).

Proof: apply `lem-pc-arrow-iso-pullback-counit` to this curve, section, family of injective
resolutions, base morphism, and class in `F(T)`. Its geometric-integrality hypothesis follows
from `prop-pc-xk-integral`: a smooth projective curve with a rational point over a separably
closed field is geometrically integral. The induced map is `baseChangeMap f i` and its module
pullback is `moduleBaseChange f i`, so that lemma's arrow isomorphism is the asserted one.
Equivalently, cohomology and base change identifies `i^* f_{T,*} L` with
`f_{T',*} i'^* L`; the comparison is compatible with counits because it is the mate of the
pullback-composition isomorphism. The tensor-pullback adjunction is the canonical one fixed
by the sectionwise unit formula in `exists_tensorPullbackAdjunction`. -/
theorem nonempty_arrowIso_moduleBaseChange_counit
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules]
    {T T' : Over (Spec (.of k))} (i : T' ⟶ T)
    (ℒ : picardInvertibleDirectImageClasses f σ hσ T) :
    let L := (fromSkeleton _).obj ℒ.1.1.val
    let L' := (Scheme.Modules.moduleBaseChange f i).obj L
    let adj := Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f T.hom))
    let adj' := Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f T'.hom))
    Nonempty (Arrow.mk ((Scheme.Modules.moduleBaseChange f i).map (adj.counit.app L)) ≅
      Arrow.mk (adj'.counit.app L')) := by
  sorry

end AlgebraicGeometry
