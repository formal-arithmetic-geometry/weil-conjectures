/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Simple
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.DeligneLaumon.AffineLine.Setup

/-!
# Irreducible middle extensions under the Fourier transform

The simple objects of the curve perverse heart are the punctual ones and the middle extensions
`(j_*M)[1]` of irreducible lisse sheaves. The Fourier transform preserves simplicity, and the
inverse transform of a punctual object is geometrically a sum of shifted linear Artin–Schreier
sheaves. So, as soon as no geometric irreducible constituent of `M` is a linear character
`ℒ_{ψ(a x)}`, the transform of `(j_*M)[1]` is again a middle extension `(j'_*M')[1]` on the
dual line. Such an `M` is called *nonexceptional*.

A nonzero linear character is ramified at infinity
(`AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier`), and the trivial one would make
`M` geometrically constant, so an irreducible `M` that is unramified at infinity and not
geometrically constant is automatically nonexceptional. Only arithmetic irreducibility is
assumed: restriction to the normal geometric subgroup of the Weil group is semisimple.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.IsNonexceptional`: the nonexceptionality condition.
- `AlgebraicGeometry.LisseOnDenseOpen.IsFourierPartner`: the relation
  `FT_ψ((j_*M)[1]) ≃ (j'_*M')[1]` between a datum and its transform.
- `AlgebraicGeometry.exists_middleExtension_fourierTransform`: the transform of an
  irreducible nonexceptional middle extension is a middle extension.
- `AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity`: the nonexceptionality test.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]

/-- Blueprint `sk-p-dl-a1-middle`: Irreducible middle extensions under Fourier. A lisse Weil
sheaf `M` on `U₀` is *nonexceptional* if none of its geometric irreducible constituents is a
linear Artin–Schreier sheaf `ℒ_{ψ(a x)}|_U`, for any `a` in an algebraic closure `k` of `k₀`,
the value `a = 0` included. -/
def WeilSheaf.IsNonexceptional {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    (ψ : AddChar k₀ (PadicAlgCl l)) (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]
    (F : WeilSheaf k₀ l U) : Prop :=
  ∀ a : k, ¬ F.HasLinearArtinSchreierConstituent ψ k a

/-- Blueprint `sk-p-dl-a1-middle`: Irreducible middle extensions under Fourier. `D'` is a
*Fourier partner* of `D` if the Fourier transform of the curve perverse middle extension
`(j_*M)[1]` of `D` is the middle extension `(j'_*M')[1]` of `D'`. -/
def LisseOnDenseOpen.IsFourierPartner (ψ : AddChar k₀ (PadicAlgCl l))
    (D D' : LisseOnDenseOpen k₀ l) : Prop :=
  Nonempty ((fourierTransform ψ).obj D.middleExtension ≅ D'.middleExtension)

variable (ψ : AddChar k₀ (PadicAlgCl l)) (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]

/-- Blueprint `sk-p-dl-a1-middle`: Irreducible middle extensions under Fourier. If `M` is a
nonzero irreducible lisse Weil sheaf on a dense open `U₀` of the affine line and is
nonexceptional, then there are a dense open `j' : U'₀ ↪ A'₀` of the dual line and a nonzero
irreducible lisse Weil sheaf `M'` on it with `FT_ψ((j_*M)[1]) ≃ (j'_*M')[1]`. -/
theorem exists_middleExtension_fourierTransform (D : LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hD : D.sheaf.IsNonexceptional ψ k) :
    ∃ D' : LisseOnDenseOpen k₀ l,
      Simple D'.sheaf ∧ ¬ IsZero D'.sheaf ∧ D.IsFourierPartner ψ D' := by
  sorry

/-- Blueprint `sk-p-dl-a1-middle`: Irreducible middle extensions under Fourier. An irreducible
lisse Weil sheaf on a dense open of the affine line which is unramified at infinity and not
geometrically constant is nonexceptional: the nonzero linear characters are excluded by their
ramification at infinity, and a geometric constant constituent of an irreducible Weil
representation forces geometric constancy. -/
theorem isNonexceptional_of_isUnramifiedAtInfinity (D : LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hinf : WeilSheaf.IsUnramifiedAtInfinity D.j D.sheaf)
    (hconst : ¬ D.sheaf.IsGeometricallyConstant) :
    D.sheaf.IsNonexceptional ψ k := by
  sorry

end AlgebraicGeometry
