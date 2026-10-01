/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Defs

/-!
# Lisse Weil sheaves on a dense open of the affine line

This file fixes the conventions of the Deligne–Laumon affine-line estimate
(`WeilConjectures.DeligneLaumon.AffineLine.Upper`) and of its auxiliary statements, following
the blueprint subsection `sk-d-dl-a1-setup`. The `ℓ`-adic formalism they are phrased against is
the provisional interface of `WeilConjectures.WeilSheaf.Defs`; what this block owns is the two
conditions on a lisse Weil sheaf on a dense open of the affine line, and the bundling of that
situation.

The affine line `A₀ = 𝔸¹_{k₀}` is `AlgebraicGeometry.affineLine k₀`, and the dual affine line
`A'₀` of the Fourier transform is another copy of it.

Both conditions below are still placeholders: they are conditions on the geometric monodromy
representation of a lisse sheaf, and neither the geometric fundamental group of a scheme nor
its action on a lisse sheaf exists in the repository yet. They carry a blueprint docstring
rather than a `TODO(unify)` tag because the subsection that owns them is this one; the object
they are waiting for is owned by `sec-purity-real-sheaves`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant`: trivial geometric monodromy.
- `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`: trivial inertia at `∞ ∈ ℙ¹`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`: a dense open immersion `j : U₀ ↪ 𝔸¹_{k₀}`
  together with a lisse Weil sheaf on `U₀`, with its direct image, its extension by zero, its
  boundary sheaf and its curve perverse middle extension.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

section Infinity

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf is *geometrically constant* if the geometric fundamental group `π₁(U ⊗ k)`
acts trivially on it; its Frobenius module may still be nontrivial.
(blueprint: `sk-d-dl-a1-setup`) -/
def IsGeometricallyConstant (F : WeilSheaf k₀ l U) : Prop := sorry

/-- A lisse Weil sheaf on an open `U₀` of the affine line is *unramified at infinity* if the
inertia group at `∞ ∈ ℙ¹` acts trivially on its geometric generic fibre; equivalently, if it
extends to a lisse Weil sheaf on an open neighbourhood of `∞` in `ℙ¹`.
(blueprint: `sk-d-dl-a1-setup`) -/
def IsUnramifiedAtInfinity (F : WeilSheaf k₀ l U) (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop := sorry

end Infinity

/-- The standing situation of the affine-line estimate: a dense open immersion
`j : U₀ ↪ 𝔸¹_{k₀}` together with a lisse Weil `ℚ̄_ℓ`-sheaf on `U₀`. Bundling the data avoids
carrying six instance arguments through every statement, and makes the existential statements
of the block — which produce a new dense open of the dual line — readable. -/
structure LisseOnDenseOpen (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] where
  /-- The dense open subscheme `U₀`. -/
  U : Scheme.{u}
  [overBase : U.Over (Spec (CommRingCat.of k₀))]
  /-- The open immersion `j : U₀ ↪ 𝔸¹_{k₀}`. -/
  j : U ⟶ affineLine k₀
  [isOpenImmersion : IsOpenImmersion j]
  [quasiCompact : QuasiCompact j]
  [isOver : j.IsOver (Spec (CommRingCat.of k₀))]
  [isDominant : IsDominant j]
  /-- The lisse Weil sheaf on `U₀`. -/
  sheaf : WeilSheaf k₀ l U
  /-- The sheaf is lisse. -/
  lisse : sheaf.IsLisse

namespace LisseOnDenseOpen

attribute [instance] overBase isOpenImmersion quasiCompact isOver isDominant

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (D : LisseOnDenseOpen k₀ l)

/-- The sheaf of the datum is unramified at infinity. -/
def IsUnramifiedAtInfinity : Prop := D.sheaf.IsUnramifiedAtInfinity D.j

/-- The sheaf of the datum is geometrically constant. -/
def IsGeometricallyConstant : Prop := D.sheaf.IsGeometricallyConstant

/-- The ordinary direct image `j_*M` of the datum, a Weil sheaf on the whole affine line. -/
noncomputable def directImage : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.directImage D.j).obj D.sheaf

/-- The extension by zero `j_!M` of the datum. -/
noncomputable def extensionByZero : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.extensionByZero D.j).obj D.sheaf

/-- The curve perverse middle extension `j_{!*}(M[1]) = (j_*M)[1]` of the datum. -/
noncomputable def middleExtension : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧

/-- The boundary sheaf `B = j_*M / j_!M`: the cokernel of the canonical map `j_!M → j_*M`, a
punctual sheaf supported on the finite complement of `U₀`. -/
noncomputable def boundarySheaf : WeilSheaf k₀ l (affineLine k₀) :=
  Limits.cokernel ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf)

/-- The shifted zero extension `j_!M[1]`, a curve perverse sheaf. -/
noncomputable def shiftedExtensionByZero : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.extensionByZero)⟦(1 : ℤ)⟧

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
