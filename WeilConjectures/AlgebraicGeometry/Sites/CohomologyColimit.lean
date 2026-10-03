/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of a direct sum on a quasi-compact quasi-separated scheme

On a quasi-compact and quasi-separated scheme `X`, étale cohomology commutes with filtered
colimits of abelian sheaves ([Stacks 03Q6]), and hence with direct sums, a direct sum being the
filtered colimit of its finite partial sums. We record the consequence used for the divisor
sequence: a direct sum of sheaves without cohomology in degree `n` has no cohomology in degree
`n`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_H_of_isColimit_cofan`: on a quasi-compact
  quasi-separated scheme, if `Hⁿ(X, Fᵢ) = 0` for all `i`, then `Hⁿ(X, ⨁ᵢ Fᵢ) = 0`. The proof is
  `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **Étale cohomology commutes with direct sums on a qcqs scheme.** Let `X` be quasi-compact
and quasi-separated and let `c` be a coproduct of a family `F` of abelian étale sheaves on `X`.
If `Hⁿ(X, Fᵢ) = 0` for all `i`, then `Hⁿ(X, c.pt) = 0`. This is the special case of direct
sums of the commutation of étale cohomology with filtered colimits on qcqs schemes,
[Stacks 03Q6]. The proof is `sorry`. -/
@[stacks 03Q6]
theorem subsingleton_H_of_isColimit_cofan (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cofan F} (hc : IsColimit c) (n : ℕ) (hF : ∀ i, Subsingleton (Sheaf.H (F i) n)) :
    Subsingleton (Sheaf.H c.pt n) :=
  sorry

end AlgebraicGeometry.Scheme
