/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.RingTheory.Kaehler.Basic

import WeilConjectures.RingTheory.PthRootFieldBaseChange
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ULift

/-! # Cotangent dimensions of a geometrically regular p-root extension

If the coefficients have independent differentials, the `p`-root quotient `B` of a geometrically
regular local algebra `A` is a regular base change of the same dimension, with finite residue
extension and the same cotangent dimension after residue extension.

## Implementation details

Adjoining `p`-th roots of the `n` coefficients gives a purely inseparable extension `k'/k` of
degree `p^n` (Tag 07DZ), and `B ≅ A ⊗_k k'` is regular. The base-change locality theorem gives a
finite free map `A → B` with finite residue extension and zero-dimensional closed fibre, so
`dim B = dim A` by the flat height formula (Tag 00ON), and the regular-local criterion identifies
dimensions with cotangent finranks. For `n = 0` the extension is `k` itself. No finiteness of
absolute differentials is used.

## References

* [Stacks, Tag 07E5] (proof of (2) ⇒ (4))
* [Stacks, Tags 07DZ, 00ON]
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Independent coefficient differentials make the p-root quotient a regular base
change of the same local dimension. Its residue extension is finite and its
cotangent dimension equals that of the lower local ring after residue extension. -/
theorem pthRoot_cotangent_dimension
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) (n : ℕ) (a : Fin n → k) :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i))
    ∀ [IsLocalRing B] [IsLocalHom (algebraMap A B)],
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
    let K := IsLocalRing.ResidueField A
    let L := IsLocalRing.ResidueField B
    Module.Finite K L ∧
      Module.finrank L (L ⊗[K] IsLocalRing.CotangentSpace A) =
        Module.finrank L (IsLocalRing.CotangentSpace B) := by
  dsimp only
  intro hlocal hmap hind
  let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i))
  obtain ⟨F, hF, hAlg, hfin, hpure, ⟨e⟩⟩ :=
    pthRootAlgebra_equiv_field_baseChange k A p n a hind
  let := hF
  let := hAlg
  let := hfin
  let := hpure
  let b := (TensorProduct.basis A (Module.finBasis k F)).map e.symm.toLinearEquiv
  have : Module.Finite A B := Module.Finite.of_basis b
  have : Module.Free A B := Module.Free.of_basis b
  have : FaithfulSMul A B := inferInstance
  have : IsRegularRing (F ⊗[k] A) := hA.2 F
  have : IsRegularRing B := IsRegularRing.of_ringEquiv
    ((TensorProduct.comm k F A).toRingEquiv.trans e.symm.toRingEquiv)
  have : IsRegularLocalRing B :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing B
  let k₀ := ULift.{v} k
  let ek : k₀ ≃ₐ[k] k := ULift.algEquiv
  have : Module.Finite k k₀ :=
    Module.Finite.of_surjective ek.symm.toLinearMap
      ek.symm.surjective
  have : IsPurelyInseparable k k₀ := ek.symm.isPurelyInseparable
  have : IsRegularRing (k₀ ⊗[k] A) := hA.2 k₀
  have : IsRegularRing A := IsRegularRing.of_ringEquiv
    ((TensorProduct.congr ek (AlgEquiv.refl : A ≃ₐ[k] A)).trans
      (TensorProduct.lid k A)).toRingEquiv
  have : IsRegularLocalRing A :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  have hd := ringKrullDim_eq_of_isIntegral A B
  have hdimA := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  have hdimB := (IsRegularLocalRing.iff_finrank_cotangentSpace B).mp inferInstance
  exact_mod_cast hdimA.trans (hd.symm.trans hdimB.symm)

end Algebra
