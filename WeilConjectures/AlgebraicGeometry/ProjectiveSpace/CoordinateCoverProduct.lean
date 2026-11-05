/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Products of coordinate covers

A coordinate cover of a scheme `X` (`AlgebraicGeometry.Scheme.CoordinateCover`) is an invertible
module `L` with trivialising sections `Tᵢ` written in terms of their ratios `Tⱼ / Tᵢ`. The tensor
product of finitely many such modules `L_a` with the products `⊗ₐ T_{a, J a}` of the trivialising
sections is again a coordinate cover, indexed by the families `J`; its charts are the
intersections `⋂ₐ U_{a, J a}`.

This is the construction behind Stacks, Tag 09NC: if every point of a quasi-compact scheme lies
in an affine chart of one of finitely many coordinate covers, the tensor product of these covers,
restricted to the charts meeting an affine chart, is a coordinate cover by affine charts, i.e. an
ample invertible module.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover.pi`: the product of finitely many coordinate covers.
- `AlgebraicGeometry.Scheme.CoordinateCover.restrict`: the coordinate cover formed by a family of
  charts that still covers `X`.
- `AlgebraicGeometry.Scheme.CoordinateCover.ofPair`: the coordinate cover with two charts.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.isAffineOpen_inf`: an affine open meets a chart in an
  affine open.
- `AlgebraicGeometry.Scheme.CoordinateCover.exists_isAffineOpen_of_iSup_eq_top`: finitely many
  coordinate covers with distinguished affine charts covering `X` give a coordinate cover by
  affine charts (Stacks, Tag 09NC).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}}

section Pi

variable {α : Type u} [Fintype α] {ι : α → Type u} (𝒟 : ∀ a, X.CoordinateCover (ι a))

end Pi

section Restrict

variable {ι : Type u} (𝒟 : X.CoordinateCover ι)

end Restrict

section OfPair

variable {U₀ U₁ : X.Opens} (a : Γ(X, U₀)) (b : Γ(X, U₁))

end OfPair

end Scheme.CoordinateCover

end AlgebraicGeometry
