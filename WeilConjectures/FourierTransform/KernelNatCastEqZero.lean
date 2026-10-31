/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier

/-! # The Fourier kernel of a global pairing

Source: the accepted DAG statement sk-def-kernel; current blueprint,
sec-fourier-transform/sk-thm-inversion/def-fd-kernel.md, defining formula
(blueprint: sk-def-kernel).

This is the ordinary small-etale construction specified by the accepted node.
The current blueprint also provides a condensed-coefficient variant, supplied by
`AlgebraicGeometry.ProEtale.condensedArtinSchreierSheafOf`; it is a different
coefficient category and is not substituted for the node's ordinary sheaf here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The Fourier kernel is `L_{Psi,b} := b^* L_Psi` on the small etale site of
`V ×_S V'`, with the same constant coefficient ring on both sites. The canonical
prime-field structure uses only `p = 0` in global sections, so the empty product
is included. `artinSchreierSheafOf` is the existing character-projector image
pulled back along the morphism represented by `b`.

For the vector-bundle application, take the finite field `k_0` of
`WeilConjectures.FourierSetting`, a bundle and its dual, and their evaluation
function as `b`. The affine-line case has rank one and `b(x,xi) = x * xi`;
rank zero gives the zero function. In both cases the function is composed with
the map to the prime-field affine line. Thus `L_{psi(x xi)}` here denotes this
prime-field construction, without asserting a comparison with the construction
over `k_0` for a trace character.

Source: accepted sk-def-kernel statement, defining formula and application;
current blueprint sec-fourier-transform/sk-thm-inversion/def-fd-kernel.md,
defining formula (blueprint: sk-def-kernel). -/
def fourierKernelOfNatCastEqZero (Λ : Type (u + 1)) [CommRing Λ]
    {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] {S V V' : Scheme.{u}}
    (π : V ⟶ S) (π' : V' ⟶ S) (h : (p : Γ(pullback π π', ⊤)) = 0)
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  letI : (pullback π π').Over (Spec (.of (ULift.{u} (ZMod p)))) :=
    ⟨(pullback π π').toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((zmodRingHomOfNatCastEqZero p h).comp ULift.ringEquiv.toRingHom))⟩
  artinSchreierSheafOf (pullback π π')
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b

end AlgebraicGeometry.Etale
