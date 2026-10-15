/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve

/-!
# The pointwise invertible-direct-image locus in the normalized Picard functor

Source: Stacks Project, Picard Schemes of Curves, Tag 0B9V
(blueprint: def-pc-f-subfunctor).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The assignment `F(T)` of normalized invertible-module classes whose derived direct image
is an invertible module in degree zero. This uses the existing `IsInvertibleDirectImage`
predicate (invertible zeroth right derived image and zero positive right derived images).
It records only the pointwise assignment; stability under base change is a separate theorem.
A normalization trivialization is not included in a class.
Source: Stacks Project, Tag 0B9V (blueprint: def-pc-f-subfunctor). -/
noncomputable def picardInvertibleDirectImageClasses {k : Type v} [Field k] {X : Scheme.{v}}
    (f : X ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules]
    (T : Over (Spec (.of k))) :
    Set ((picardFunctorNormalized f σ hσ).toFunctor.obj (op T)) :=
  {L | IsInvertibleDirectImage f T L.1}

end AlgebraicGeometry
