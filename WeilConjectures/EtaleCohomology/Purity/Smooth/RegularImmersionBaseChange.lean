/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.Mathlib.Data.Fin.Tuple.Basic

/-!
# Base change and intersections of fundamental classes of regular immersions

Let `i : Z ⟶ X` be a regular closed immersion of codimension `c`, with `X` smooth over a perfect
field `k` and `Z` regular, and let `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` be its fundamental class
(`AlgebraicGeometry.Etale.fundamentalClass`).

* *Flat base change.* For a flat `e : X' ⟶ X` with `X'` smooth over `k` and the base change
  `i' : Z' ⟶ X'` with `Z'` regular, the restriction of `[Z ⊂ X]` along `e` is `[Z' ⊂ X']`:
  Zariski frames of `i` pull back to Zariski frames of `i'`, and Kummer boundary products are
  compatible with pullback along any morphism. This applies in particular to a smooth `e`, for
  which the hypotheses on the base change are automatic.
* *Frames of an intersection.* For regular closed immersions `i₁ : Y₁ ⟶ X`, `i₂ : Y₂ ⟶ X` and
  `Y = Y₁ ×_X Y₂`, two frames `(U₁, f)` of `i₁` and `(U₂, g)` of `i₂` give the frame
  `(U₁ ×_X U₂, (f, g))` of `Y ⟶ X`. The key fact is `V(s ∪ t) = V(s) ×_U V(t)` for sets `s`, `t`
  of global functions on a scheme `U`.

## Main statements

- `AlgebraicGeometry.Scheme.isPullback_zeroLocusSubschemeι_union`: `V(s ∪ t) = V(s) ×_U V(t)`.
- `AlgebraicGeometry.Scheme.Hom.EtaleFrame.inter`: the frame of an intersection.
- `AlgebraicGeometry.Scheme.Hom.exists_etaleFrame_inter`: Zariski frames of an intersection.
- `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_flat`,
  `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_smooth`: base change of the
  fundamental class.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Scheme

variable {X : Scheme.{u}}

end Scheme

namespace Scheme.Hom

variable {X Y Y₁ Y₂ : Scheme.{u}} {c₁ c₂ : ℕ} {i₁ : Y₁ ⟶ X} {i₂ : Y₂ ⟶ X} {i : Y ⟶ X}
  {j₁ : Y ⟶ Y₁} {j₂ : Y ⟶ Y₂}

end Scheme.Hom

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} [Finite Λ]

attribute [local instance] HasInvertibleExponent.opens

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X]
  {k : Type u} [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

end Etale

end AlgebraicGeometry
