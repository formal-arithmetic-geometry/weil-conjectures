/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.GeometricallyRegularDifferentialFamily
import WeilConjectures.RingTheory.JacobiZariskiConnectingMapNaturality
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Field.ULift

/-!
# Geometric regularity and the first cotangent homology of the residue field

A geometrically regular Noetherian local algebra `A` over a field `k` of positive
characteristic is regular local, and the map `H₁(L_{K/k}) → m/m²` is injective, where `m` is
the maximal ideal and `K` the residue field.

## Implementation details

By the Jacobi-Zariski sequence and vanishing of `H₁` for fields of characteristic `p`, it
suffices that the comparison of differentials `K ⊗ Ω_k → K ⊗ Ω_A` is injective, i.e. that the
images of a finite independent family `da₁, …, daₙ` stay independent. Adjoining the `p`-th
roots of the `aᵢ` gives a finite purely inseparable extension `k'` of degree `pⁿ`, and
`A' = A ⊗ k'` is regular local of the same dimension as `A`. Comparing the conormal sequences
of `A` and `A'` (tensored with the flat extension `K'/K`) with the snake lemma and the Cartier
equality shows that the kernel of the comparison of absolute differentials, spanned by the
`daᵢ`, has dimension `n`.

## References

* [Stacks, Tag 07E5]
-/

@[expose] public section

universe u v

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- A geometrically regular Noetherian local algebra over a field of positive characteristic
is regular local, and the canonical map from the first cotangent homology of its residue field
into the maximal ideal modulo its square is injective. The residue field is the canonical
quotient `K = A / maximalIdeal A`. The map is the composite of `H1Cotangent.map k A K K`
with the surjection-to-conormal equivalence for `A → K`; the latter's target is the cotangent
module of the kernel of the residue map, namely the maximal ideal modulo its square.
-/
theorem isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) :
    let K := IsLocalRing.ResidueField A
    let P := Extension.ofSurjective (Algebra.ofId A K) (IsLocalRing.residue_surjective)
    IsRegularLocalRing A ∧
      Function.Injective
        (P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)) := by
  classical
  let K := A ⧸ IsLocalRing.maximalIdeal A
  let : Field K :=
    { (inferInstance : CommRing K), Ideal.Quotient.field (IsLocalRing.maximalIdeal A) with }
  let k' := ULift.{v} k
  have : IsPurelyInseparable k k' := (ULift.algEquiv : k' ≃ₐ[k] k).symm.isPurelyInseparable
  have : IsRegularRing (TensorProduct k k' A) := hA.2 k'
  have : IsRegularRing A := IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.congr (ULift.algEquiv : k' ≃ₐ[k] k)
      (AlgEquiv.refl : A ≃ₐ[k] A)).trans (Algebra.TensorProduct.lid k A)).toRingEquiv
  refine ⟨IsRegularLocalRing.of_isRegularRing_of_isLocalRing A, ?_⟩
  let := ZMod.algebra k p
  let := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  have : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨c, hc, hcomm, _⟩ := jacobiZariski_connectingMap_naturality
    (ZMod p) k A (IsLocalRing.maximalIdeal A)
  have hcinj : Function.Injective c := by
    obtain ⟨ι, a, _, hspan, hli⟩ := exists_linearIndependent' k
      (KaehlerDifferential.D (ZMod p) k)
    rw [KaehlerDifferential.span_range_derivation] at hspan
    let b := Module.Basis.mk hli (by rw [hspan])
    apply LinearMap.injective_of_linearIndependent (b.baseChange K).span_eq
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have hi := linearIndependent_residueField_differentials_of_isGeometricallyRegular
      k A p hA s (fun i ↦ a i.val) (hli.comp _ Subtype.val_injective)
    convert hi using 1
    all_goals first
      | rfl
      | (ext i
         simp only [Function.comp_apply, Module.Basis.baseChange_apply]
         dsimp only [b]
         rw [Module.Basis.mk_apply]
         exact hc 1 (a i.val))
  have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : Subsingleton (H1Cotangent (ZMod p) K) := by
    have he : ZMod.algebra K p = (inferInstance : Algebra (ZMod p) K) :=
      Subsingleton.elim _ _
    convert subsingleton_h1Cotangent_of_charP p (Fact.out : p.Prime).pos K using 1
    congr 1
    exact he.symm
  apply (Extension.ofSurjective (Algebra.ofId A (IsLocalRing.ResidueField A))
    IsLocalRing.residue_surjective).h1CotangentEquivCotangent.injective.comp
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change H1Cotangent.map k A K K x = 0 at hx
  have hx' : c (H1Cotangent.δ (ZMod p) k K x) = 0 := by
    have hh := LinearMap.congr_fun hcomm x
    let Q := Extension.ofSurjective (IsScalarTower.toAlgHom (ZMod p) A K)
      (Ideal.Quotient.mk_surjective : Function.Surjective
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
    have hz : Q.h1CotangentEquivCotangent (H1Cotangent.map k A K K x) = 0 :=
      (congrArg Q.h1CotangentEquivCotangent hx).trans
        Q.h1CotangentEquivCotangent.map_zero
    exact hh.symm.trans ((congrArg Q.cotangentComplex hz).trans Q.cotangentComplex.map_zero)
  have hδ : H1Cotangent.δ (ZMod p) k K x = 0 :=
    hcinj (hx'.trans (map_zero c).symm)
  obtain ⟨y, hy⟩ := (H1Cotangent.exact_map_δ (ZMod p) k K x).mp hδ
  exact hy.symm.trans ((congrArg (H1Cotangent.map (ZMod p) k K K)
    (Subsingleton.elim y 0)).trans (H1Cotangent.map (ZMod p) k K K).map_zero)

end Algebra
