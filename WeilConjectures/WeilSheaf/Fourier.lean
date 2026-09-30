/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.Category

/-!
# Artin–Schreier sheaves and the Fourier–Deligne transform

Placeholders with `sorry` bodies; see `WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.artinSchreier` and `AlgebraicGeometry.fourierTransform`: the
  Artin–Schreier sheaves and the Fourier–Deligne transform of the affine line.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

-- TODO(unify): sk-def-as
/-- The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line: the `ψ`-isotypic part of the
pushforward of the constant sheaf along the Artin–Schreier cover `u^q - u = a x`, which is
Galois over the line with group `k₀`, so that its isotypic components are indexed by the
additive characters of `k₀`. It is lisse of rank one and of weight zero. -/
noncomputable def artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    WeilSheaf k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
/-- The Fourier–Deligne transform `FT_ψ` from the bounded derived category of Weil complexes
on the affine line to that of the dual affine line, with Laumon's shift by the relative
dimension one. -/
noncomputable def fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
instance (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierTransform (l := l) ψ).Additive := sorry

-- TODO(unify): sk-thm-inversion
/-- Fourier inversion: for a nontrivial additive character the Fourier–Deligne transform is an
equivalence of the bounded derived categories of the two dual lines. Owned by the blueprint
block `sec-fourier-transform`; see `WeilConjectures.WeilSheaf.Defs`. -/
theorem isEquivalence_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ).IsEquivalence := sorry

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-operations
/-- `F.HasLinearArtinSchreierConstituent ψ a` says that the restriction to `U` of the geometric
linear Artin–Schreier sheaf `ℒ_{ψ(a x)}`, for `a` in the algebraic closure of `k₀`, is an
irreducible constituent of the pullback of `F` to `U ⊗_{k₀} k`. The geometric sheaf is defined
over the finite subextension `k₀(a)`, where it is `AlgebraicGeometry.artinSchreier` for the
character `ψ ∘ Tr`; only its pullback to the geometric affine line is used here. -/
def WeilSheaf.HasLinearArtinSchreierConstituent (F : WeilSheaf k₀ l U)
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) : Prop := sorry

end AlgebraicGeometry
