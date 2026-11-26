/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.PthRootResidueDimensionBalance
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Finite independent differential families in geometrically regular local algebras

In a geometrically regular local algebra over a field `k` of characteristic `p`, a finite
family of elements of `k` with independent differentials keeps independent differentials
after base change to the residue field.

## Implementation details

The proof adjoins `p`-th roots `k[X_i]/(X_i^p - a_i)` of the family and compares the conormal
exact sequences of `A` and of its base change `A'`; both are regular local of the same
dimension. A dimension count with the snake lemma shows that the kernel of the comparison of
absolute differentials, spanned by the `1 ⊗ da_i`, has dimension `n`. No finiteness of the
whole module of absolute differentials is assumed.

## References

* [Stacks, Tag 07E5]
* [Stacks, Tag 07DZ]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A finite independent family of prime-field differentials in the base field stays
independent in the residue-field base change of the algebra's prime-field differentials. -/
theorem linearIndependent_residueField_differentials_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) (ι : Type w) [Finite ι] (a : ι → k) :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
      LinearIndependent (IsLocalRing.ResidueField A) (fun i ↦
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D (ZMod p) A (algebraMap k A (a i))) := by
  classical
  let := ZMod.algebra k p
  let := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  intro hind
  let := Fintype.ofFinite ι
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let a' : Fin n → k := a ∘ e
  have hind' : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a' i)) :=
    hind.comp e e.injective
  let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a' i))
  obtain ⟨hlocal, hmap, hker, hcoker⟩ :=
    pthRoot_residue_differentials p n A (fun i ↦ algebraMap k A (a' i))
  let : IsLocalRing B := hlocal
  have : IsLocalHom (algebraMap A B) := hmap
  let L := IsLocalRing.ResidueField B
  have hbalance := pthRoot_residue_dimension_balance k A p hA n a' hind'
  have hext : LinearIndependent L (fun i : Fin n ↦
      (1 : L) ⊗ₜ[A] KaehlerDifferential.D (ZMod p) A (algebraMap k A (a' i))) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Fintype.card_fin]
    change n = Module.finrank L (Submodule.span L (Set.range (fun i : Fin n ↦
      (1 : L) ⊗ₜ[A] KaehlerDifferential.D (ZMod p) A (algebraMap k A (a' i)))))
    rw [← hker, hbalance, hcoker]
  let K := IsLocalRing.ResidueField A
  let M := KaehlerDifferential (ZMod p) A
  let f : K ⊗[A] M →ₗ[K] L ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.map
      ((Algebra.linearMap K L) : K →ₗ[K] L) (LinearMap.id : M →ₗ[A] M)
  have hdown : LinearIndependent K (fun i : Fin n ↦
      (1 : K) ⊗ₜ[A] KaehlerDifferential.D (ZMod p) A (algebraMap k A (a' i))) := by
    apply LinearIndependent.of_comp f
    simpa [f, Function.comp_def] using hext.restrict_scalars' K
  exact (linearIndependent_equiv e).mp hdown

end Algebra
