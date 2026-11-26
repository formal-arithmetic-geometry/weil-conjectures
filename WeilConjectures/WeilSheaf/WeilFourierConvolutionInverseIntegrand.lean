/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# Multiplication of inverse-character integrands

This file shows that tensoring with the Artin–Schreier sheaves for `a` and for `b` with the
inverse character is tensoring with the Artin–Schreier sheaf for `a - b`. This is the first step
of the computation of the Fourier convolution kernel.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

/-- Tensoring with the two character sheaves for `a` and `b`, with inverse characters,
is tensoring with the character sheaf for `a - b`, naturally in the input complex. -/
theorem nonempty_iso_tensorLisse_artinSchreierOf_sub
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (ψ : AddChar k₀ (PadicAlgCl l)) (a b : Γ(X, ⊤)) :
    Nonempty (tensorLisse (artinSchreierOf ψ a) (isLisse_artinSchreierOf ψ a) ⋙
        tensorLisse (artinSchreierOf ψ⁻¹ b) (isLisse_artinSchreierOf ψ⁻¹ b) ≅
      tensorLisse (artinSchreierOf ψ (a - b)) (isLisse_artinSchreierOf ψ (a - b))) := by
  obtain ⟨eInv⟩ := nonempty_iso_artinSchreierOf_inv ψ b
  obtain ⟨eT⟩ := nonempty_iso_tensorLisse_of_iso eInv
    (isLisse_artinSchreierOf ψ⁻¹ b) (isLisse_artinSchreierOf ψ (-b))
  obtain ⟨eComp⟩ := nonempty_iso_tensorLisse_comp
    (artinSchreierOf ψ (-b)) (artinSchreierOf ψ a)
    (isLisse_artinSchreierOf ψ (-b)) (isLisse_artinSchreierOf ψ a)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ (-b) a
  obtain ⟨eSub⟩ := nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) (by abel : -b + a = a - b)))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ (-b)).dual
      (isLisse_artinSchreierOf ψ a))
    (isLisse_artinSchreierOf ψ (a - b))
  exact ⟨Functor.isoWhiskerLeft _ eT ≪≫ eComp ≪≫ eSub⟩

end AlgebraicGeometry.WeilComplex
