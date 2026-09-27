/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Compactification.Defs

/-!
# Smooth proper completion of a smooth curve over a finite field

A smooth geometrically connected curve `U₀` over a finite field `K = 𝔽_q` embeds as a dense
open subscheme of a curve `C₀` which is *proper* over `K` and still smooth and geometrically
connected, the boundary `C₀ \ U₀` being a finite set of closed points.

Separatedness of `U₀` over `K` is part of `AlgebraicGeometry.IsCurve` and is necessary: a
compactification of `p` forces `p` to be separated
(`AlgebraicGeometry.Compactification.isSeparated`), so the affine line with doubled origin has
none.

The proof, which is not formalised here, runs as follows. Nagata's compactification theorem
embeds `U₀` into some scheme proper over `K`; replacing that scheme by the scheme-theoretic
closure `X` of `U₀` gives an integral proper `K`-scheme of dimension one containing `U₀` as a
dense open. The complement `X \ U₀` is then a proper closed subset of an integral
one-dimensional scheme of finite type over a field, hence a finite set of closed points.
Normalising, `C₀ = X^ν → X` is finite, surjective and birational, so `C₀` is again proper of
dimension one; being normal of dimension one it is regular, and a regular scheme of finite type
over the perfect field `𝔽_q` is smooth. As `U₀` is smooth, hence normal, the normalisation is an
isomorphism over `U₀`, so `U₀ → C₀` is an open immersion whose complement is the preimage of the
finite set `X \ U₀` under a finite morphism. Finally `C₀` is geometrically connected because the
geometric base change of `U₀` is connected and dense in that of `C₀`.

## Main statements

- `AlgebraicGeometry.exists_smooth_properCompactification`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `sk-i-real-compactification`: Smooth proper completion.

Every smooth geometrically connected curve `U₀` over a finite field `K` admits a smooth proper
completion: a compactification `c : Compactification p` of the structure morphism
`p : U₀ ⟶ Spec K` whose ambient scheme `c.Z = C₀` is again a smooth geometrically connected
curve over `K`, and whose boundary `C₀ \ U₀` is a finite set of closed points of `C₀`.

The open immersion `U₀ ⟶ C₀` and the properness of `C₀ ⟶ Spec K` are part of the data of a
`Compactification`, so they do not appear among the conclusions. -/
theorem exists_smooth_properCompactification
    {K : Type u} [Field K] [Finite K] {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] :
    ∃ c : Compactification p, IsCurve c.g ∧ SmoothOfRelativeDimension 1 c.g ∧
      GeometricallyConnected c.g ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  sorry

end AlgebraicGeometry
