/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.FourierTransform.ArtinSchreierFiniteLisse
public import Sheaf.Paper.FourierSetting

/-!
# The Fourier kernel, including empty fiber products

Source: main-20261015 blueprint, `sec-fourier-transform/sk-def-kernel/_section.md`
(blueprint: sk-def-kernel).

The kernel is the prime-field Artin–Schreier sheaf of the pairing. The condition
`p = 0` in global sections supplies the canonical prime-field structure even on
an empty fiber product; it does not require its global ring to have characteristic `p`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The Fourier kernel `K_psi := L_{Psi,b} = b^* L_Psi`, as an étale sheaf of
`Λ`-modules on `V ×_S V'`, using the canonical prime-field structure supplied by
`h`. The equality is definitional: `artinSchreierSheafOfNatCastEqZero` applies
`artinSchreierSheafOf`, the inverse image of `artinSchreierSheaf` along the morphism
represented by the global function `b`.

For a vector bundle over `S₀` and its dual, take `b` to be their evaluation pairing.
For rank one over `Spec k₀`, take `b = x ξ`. The resulting notation `L_{psi(x ξ)}`
means this prime-field sheaf, with the map to the affine line over `k₀` followed by
its map to the affine line over `F_p`. It does not denote the construction over
`k₀` using a trace character. The finite field `k₀` may be taken from
`WeilConjectures.FourierSetting.field`; no adic coefficient condition is imposed here.

Source: main-20261015 blueprint, `sec-fourier-transform/sk-def-kernel/_section.md`
(blueprint: sk-def-kernel). -/
noncomputable def fourierKernelOfNatCastEqZero
    (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (h : (p : Γ(pullback π π', ⊤)) = 0) (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  artinSchreierSheafOfNatCastEqZero h Ψ b

end AlgebraicGeometry.Etale
