/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Complexes of finite free modules given by matrices

Let `S` be a commutative ring and `r : ℤ → ℕ`. A *matrix complex* of ranks `r` over `S`
(`MatrixComplex r S`) is a family of matrices `d i` of size `r (i + 1) × r i` with
`d (i + 1) * d i = 0`. It defines a cochain complex `M.complex` of `S`-modules with terms
`Sʳ⁽ⁱ⁾` (`MatrixComplex.complex`).

Matrix complexes are convenient for base change and limits: the base change along a ring
morphism `φ : S →+* S'` is given by the reduced matrices (`MatrixComplex.map`), and the
reduction `Sʳ⁽ⁱ⁾ ⟶ S'ʳ⁽ⁱ⁾` is a chain map (`MatrixComplex.reduction`). When `φ` is surjective
with principal kernel and the ranks are bounded, this reduction exhibits the reduced complex as
the derived base change (`MatrixComplex.isDerivedBaseChange_reduction`).

## Main definitions

- `MatrixComplex`: matrix complexes.
- `MatrixComplex.complex`: the associated cochain complex.
- `MatrixComplex.homMk`: chain maps given by matrices.
- `MatrixComplex.map`: base change of matrix complexes.
- `MatrixComplex.reduction`: the reduction chain map.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace MatrixComplex

variable {r r' r'' : ℤ → ℕ} {S : Type u} [CommRing S] (M : MatrixComplex r S)

/-! ### Chain maps given by matrices -/

variable {M} {N : MatrixComplex r' S} {P : MatrixComplex r'' S}

/-! ### Base change -/

variable {S' : Type u} [CommRing S'] (φ : S →+* S')

variable [HasDerivedCategory.{u} (ModuleCat.{u} S)] [HasDerivedCategory.{u} (ModuleCat.{u} S')]

end MatrixComplex

/-! ### Alternating sums of traces -/

