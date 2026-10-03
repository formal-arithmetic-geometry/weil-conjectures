/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-!
# The `n`-torsion of an abelian variety

For `n` prime to the characteristic, the `n`-torsion subgroup scheme of an abelian variety is
étale; over an algebraically closed field its points do not change under extension of
algebraically closed fields, and for an abelian variety of dimension `g` the group of
`n`-torsion points is `(ℤ/nℤ) ^ (2 * g)`.

The group `A(K)` of `K`-points of `A` is `𝟙_ (Over (Spec (.of K))) ⟶ A` with the group structure
of `CategoryTheory.GrpObj.Hom.group`; it is written additively as
`Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)`, so that `AddSubgroup.torsionBy` describes its
`n`-torsion.

"Prime to the characteristic" is spelled `¬ p ∣ n`, which for `p = 0` says exactly `n ≠ 0`.

## Main statements

- `AlgebraicGeometry.etale_torsionSubgroupScheme`: the `n`-torsion of an abelian variety is
  étale for `n` prime to the characteristic.
- `AlgebraicGeometry.bijective_toUnit_comp_torsionSubgroupScheme`: its points do not change
  under an extension of algebraically closed fields.
- `AlgebraicGeometry.nonempty_addEquiv_torsionBy`: `A(K)[n] ≃+ (ℤ/nℤ) ^ (2 * g)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-ntorsion-etale`: The `n`-torsion of an abelian variety is étale.

Let `A` be an abelian variety over a field `K` of characteristic `p` and let `n` be prime to
`p`. Then `A[n]` is an étale group scheme over `K`. -/
theorem etale_torsionSubgroupScheme (p : ℕ) [CharP K p] (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianScheme A] (n : ℕ) (hn : 0 < n) (hnp : ¬ p ∣ n) :
    Etale (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-ntorsion-etale`: The `n`-torsion of an abelian variety is étale.

For `n` prime to the characteristic of an algebraically closed base field `K`, the canonical
base-change map `A[n](K) ⟶ A[n](K')` is a bijection for every extension `K ⊆ K'` of
algebraically closed fields. -/
theorem bijective_toUnit_comp_torsionSubgroupScheme [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] (n : ℕ) (hn : 0 < n)
    (hnp : ¬ p ∣ n) (K' : Type u) [Field K'] [Algebra K K'] [IsAlgClosed K'] :
    Function.Bijective
      (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme A n ↦
        toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) :=
  sorry

/-- Blueprint `sk-prop-av-ntorsion-etale`: The `n`-torsion of an abelian variety is étale.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` of
characteristic `p` and let `n` be prime to `p`. Then `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)`. -/
theorem nonempty_addEquiv_torsionBy [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] (n : ℕ) (hn : 0 < n)
    (hnp : ¬ p ∣ n) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * IsAbelianScheme.dim A) → ZMod n)) :=
  sorry

end AlgebraicGeometry
