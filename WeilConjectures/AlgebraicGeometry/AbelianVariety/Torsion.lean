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
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

/-!
# The `n`-torsion of an abelian variety

Over an algebraically closed field and for `n` prime to the characteristic, the `n`-torsion
subgroup scheme of an abelian variety of dimension `g` is finite étale, its points do not change
under extension of algebraically closed fields, and the group of points is `(ℤ/nℤ) ^ (2 * g)`.

The group `A(K)` of `K`-points of `A` is `𝟙_ (Over (Spec (.of K))) ⟶ A` with the group structure
of `CategoryTheory.GrpObj.Hom.group`; it is written additively as
`Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)`, so that `AddSubgroup.torsionBy` describes its
`n`-torsion.

## Main statements

- `AlgebraicGeometry.etale_torsionSubgroupScheme`: the `n`-torsion of an abelian variety is
  étale.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-ntorsion-etale`: The `n`-torsion of an abelian variety is étale.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let `n`
be prime to `char K`. Then `A[n]` is a finite étale group scheme over `K`, the canonical base
change map `A[n](K) ⟶ A[n](K')` is an isomorphism for every extension `K ⊆ K'` of algebraically
closed fields, and `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)`. -/
theorem etale_torsionSubgroupScheme [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [IsAbelianVariety A] (g n : ℕ)
    (hg : topologicalKrullDim A.left = (g : ℕ∞)) (hn : 1 ≤ n)
    (hnp : p = 0 ∨ ¬ (p ∣ n)) (K' : Type u) [Field K'] [Algebra K K'] [IsAlgClosed K'] :
    IsFinite (torsionSubgroupScheme A n).hom ∧ Etale (torsionSubgroupScheme A n).hom ∧
      Function.Bijective
        (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme A n =>
          toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) ∧
      Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) (n : ℤ) ≃+
        (Fin (2 * g) → ZMod n)) :=
  sorry

end AlgebraicGeometry
