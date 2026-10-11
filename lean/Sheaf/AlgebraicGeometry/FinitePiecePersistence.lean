/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Persistence of a finite open piece under residue-field-preserving base change

Source: Stacks Project, More on Morphisms, Tag 02LK, final assertion
(blueprint: lem-weil-pbc-elementary-etale-finite-piece-persistence).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite open piece with a unique point above `u` and unchanged residue field at `x`
persists under any base change preserving the residue field at `u`.
Source: Stacks Project, Tag 02LK, final assertion; the generalization to arbitrary `ψ`
uses no étaleness (blueprint: lem-weil-pbc-elementary-etale-finite-piece-persistence).

Proof for stage 3:
1. The square with projections `π` and `pullback.snd f (ψ ≫ φ)` is cartesian by
`lem-weil-pbc-cartesian-square-pasting`, using the two specified fibre products
(`def-pc-fibre-product`).
2. By `lem-weil-pbc-open-fibre-product`, the inverse-image open is the base change
of `V` over `U`. Finiteness follows from `lem-weil-pbc-finite-morphism-permanence`.
3. Every point of this open above `u'` maps to `v`, by uniqueness above `u`.
By `lem-weil-pbc-fibre-product-points`, these points correspond to the spectrum of
κ(v) ⊗[κ(u)] κ(u'). The residue-field isomorphism for `ψ` identifies this tensor
product with κ(v), a field, so there is exactly one such point.
4. By `lem-weil-pbc-fibre-product-point-residue-field`, its residue field is the same
field κ(v), compatibly with `π`. Compose its residue-field isomorphism with the
one for `V.ι ≫ pullback.fst f φ` to obtain the asserted isomorphism at `x`.
Residue-field maps here are those of `def-weil-residue-field`. -/
theorem finitePiece_persistence_of_isIso_residueFieldMap
    {X S U U' : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S)
    (u₀ : U) (x : X) (hx : f x = φ u₀)
    (V : (pullback f φ).Opens) (v : V.toScheme)
    (hfinite : IsFinite (V.ι ≫ pullback.snd f φ))
    (hv : (V.ι ≫ pullback.snd f φ) v = u₀)
    (hunique : ∀ w : V.toScheme, (V.ι ≫ pullback.snd f φ) w = u₀ → w = v)
    (hvx : (V.ι ≫ pullback.fst f φ) v = x)
    (hresidue : IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v))
    (ψ : U' ⟶ U) (u₁ : U') (hu : ψ u₁ = u₀)
    (hbase : IsIso (ψ.residueFieldMap u₁))
    (π : pullback f (ψ ≫ φ) ⟶ pullback f φ)
    (hπp : π ≫ pullback.fst f φ = pullback.fst f (ψ ≫ φ))
    (hπq : π ≫ pullback.snd f φ = pullback.snd f (ψ ≫ φ) ≫ ψ) :
    let V' := π ⁻¹ᵁ V
    IsFinite (V'.ι ≫ pullback.snd f (ψ ≫ φ)) ∧
      ∃ v' : V'.toScheme,
        (V'.ι ≫ pullback.snd f (ψ ≫ φ)) v' = u₁ ∧
        (∀ w : V'.toScheme, (V'.ι ≫ pullback.snd f (ψ ≫ φ)) w = u₁ → w = v') ∧
        (V'.ι ≫ pullback.fst f (ψ ≫ φ)) v' = x ∧
        IsIso ((V'.ι ≫ pullback.fst f (ψ ≫ φ)).residueFieldMap v') ∧
        π (V'.ι v') = V.ι v := by
  sorry

end AlgebraicGeometry
