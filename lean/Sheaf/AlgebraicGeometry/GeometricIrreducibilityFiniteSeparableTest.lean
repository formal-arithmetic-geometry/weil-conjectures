/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Adjoin.FGBaseChange
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.FieldTheory.SepClosedAlgebrasTensorIrreducible

/-!
# Testing geometric irreducibility on finite separable extensions

Source: Stacks Project, Algebra, Tag 037K, `lemma-geometrically-irreducible`,
equivalence of (1) and (2)
(blueprint: lem-zl-geometric-irreducibility-finite-separable-test).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem spec_irreducible_of_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at *
  have heq : nilradical A = (nilradical B).comap f := by
    ext x
    change IsNilpotent x ↔ IsNilpotent (f x)
    constructor
    · exact fun h ↦ h.map f
    · rintro ⟨n, hn⟩
      exact ⟨n, hf (by simpa only [map_pow, map_zero] using hn)⟩
  rw [heq]
  exact Ideal.IsPrime.comap f

private theorem lift_pair_separable
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (x y : R ⊗[k] K) :
    ∃ (E : IntermediateField k K), FiniteDimensional k E ∧
      ∃ x' y' : R ⊗[k] E,
        TensorProduct.map (AlgHom.id R R) E.val x' = x ∧
        TensorProduct.map (AlgHom.id R R) E.val y' = y := by
  obtain ⟨B, hB, x', hx⟩ := exists_fg_and_mem_baseChange x
  obtain ⟨C, hC, y', hy⟩ := exists_fg_and_mem_baseChange y
  let D := B ⊔ C
  have : Algebra.IsAlgebraic k D :=
    Algebra.IsAlgebraic.of_injective D.val Subtype.val_injective
  let E := Algebra.IsAlgebraic.toIntermediateField D
  have : Algebra.FiniteType k D := D.fg_iff_finiteType.mp (hB.sup hC)
  have : FiniteDimensional k E := Algebra.IsIntegral.finite (R := k) (A := D)
  refine ⟨E, inferInstance,
    TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_left) x',
    TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_right) y', ?_, ?_⟩
  · change TensorProduct.map (AlgHom.id R R) B.val x' = x at hx
    change TensorProduct.map (AlgHom.id R R) D.val
      (TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_left) x') = x
    change ((TensorProduct.map (AlgHom.id R R) D.val).comp
      (TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_left))) x' = x
    rw [← TensorProduct.map_id_comp]
    exact hx
  · change TensorProduct.map (AlgHom.id R R) C.val y' = y at hy
    change TensorProduct.map (AlgHom.id R R) D.val
      (TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_right) y') = y
    change ((TensorProduct.map (AlgHom.id R R) D.val).comp
      (TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_right))) y' = y
    rw [← TensorProduct.map_id_comp]
    exact hy

private theorem spec_tensor_separableClosure
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
      [Algebra.IsSeparable k E], IrreducibleSpace (PrimeSpectrum (R ⊗[k] E))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := by
  have hk := h k
  have : Nontrivial (R ⊗[k] k) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hk.toNonempty
  have : Nontrivial R := (TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] k).domain_nontrivial
  have : Nontrivial (R ⊗[k] SeparableClosure k) := inferInstance
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  refine ⟨?_, ?_⟩
  · exact fun htop ↦ bot_ne_top (Ideal.radical_eq_top.mp htop)
  · intro x y hxy
    obtain ⟨E, hE, x', y', hx, hy⟩ := lift_pair_separable k R (SeparableClosure k) x y
    have := hE
    have hEirr := h E
    have hprime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hEirr
    let f := TensorProduct.map (AlgHom.id R R) E.val
    have hf : Function.Injective f :=
      Module.Flat.lTensor_preserves_injective_linearMap E.val.toLinearMap E.val.injective
    have hprod : x' * y' ∈ nilradical (R ⊗[k] E) := by
      obtain ⟨n, hn⟩ := mem_nilradical.mp hxy
      apply mem_nilradical.mpr
      refine ⟨n, hf ?_⟩
      simpa only [map_pow, map_mul, map_zero, f, hx, hy] using hn
    rcases hprime.mem_or_mem hprod with hxnil | hynil
    · exact Or.inl (mem_nilradical.mpr (hx ▸ (mem_nilradical.mp hxnil).map f))
    · exact Or.inr (mem_nilradical.mpr (hy ▸ (mem_nilradical.mp hynil).map f))

/-- For an arbitrary commutative algebra over a field, irreducibility of its spectrum after
all field extensions is equivalent to irreducibility after all finite separable extensions.
The tensor-product ring has `(r ⊗ a) * (s ⊗ b) = (r * s) ⊗ (a * b)` and unit `1 ⊗ 1`.
`IrreducibleSpace` includes nonemptiness. No reducedness or finite generation is assumed.

Source: Stacks Project, Algebra, Tag 037K, equivalence (1) and (2)
(blueprint: lem-zl-geometric-irreducibility-finite-separable-test).

Proof:
1. Specializing the universal condition to finite separable extensions proves the forward
   implication.
2. For fields `k ⊆ E ⊆ F`, tensor balancing gives mutually inverse ring isomorphisms
   `(R ⊗[k] E) ⊗[E] F ≃ R ⊗[k] F`, sending `(r ⊗ e) ⊗ f` to `r ⊗ (e * f)`
   and `r ⊗ f` to `(r ⊗ 1) ⊗ f`. Multiplication and units agree by
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`. Scalar extension is injective:
   apply `lem-weil-pbc-field-extension-base-change-faithfully-flat` and the zero-ideal case
   of `lem-weil-pbc-faithfully-flat-ideal-contraction`. Similarly `R ⊗[k] k ≃ R`.
3. Assuming the finite separable tests, choose a separable closure `ks/k`
   (`def-pd-separable-closure`). The test at `E = k` makes `Spec R` irreducible and hence
   `R` nonzero by `lem-zl-spectrum-irreducible-nilradical-prime`. Injectivity in step 2
   makes `A = R ⊗[k] ks` nonzero, so its nilradical is proper.
4. If `x * y` in `A` is nilpotent, express `x` and `y` as finite sums of pure tensors
   (`def-weil-pbc-module-tensor-product`). All coefficients lie in one finite separable
   subextension `E/k` of `ks/k`. Lift to `xE,yE` in `R ⊗[k] E`; injectivity in step 2
   detects the nilpotence equation there. The finite separable test and
   `lem-zl-spectrum-irreducible-nilradical-prime` imply that `xE` or `yE` is nilpotent.
   Thus `x` or `y` is nilpotent, the nilradical of `A` is prime, and `Spec A` is irreducible.
5. For any extension `L/k`, use `lem-weil-common-extension-fields` to embed `L` and `ks`
   compatibly over `k` into a field `M`. The spectrum of `M` is irreducible, since its
   nilradical is the proper prime zero ideal. Apply
   `lem-zl-sepclosed-algebras-tensor-irreducible` over the separably closed field `ks`
   to `A` and `M`. It makes `Spec (A ⊗[ks] M)` irreducible; step 2 identifies this
   tensor product with `C = R ⊗[k] M`.
6. Step 2 gives an injective unital map `B = R ⊗[k] L → C`. Injectivity reflects
   nilpotence, so the nilradical of `B` is the inverse image of the nilradical of `C`.
   The latter is proper prime by `lem-zl-spectrum-irreducible-nilradical-prime`.
   Its inverse image is proper prime, and the same criterion makes `Spec B` irreducible.
   This proves the condition for every `L/k`.
-/
theorem irreducibleSpace_tensorProduct_iff_finite_separable
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    (∀ (L : Type (max u v w)) [Field L] [Algebra k L],
      IrreducibleSpace (AlgebraicGeometry.Spec (CommRingCat.of (R ⊗[k] L)))) ↔
    (∀ (E : Type (max u v w)) [Field E] [Algebra k E] [FiniteDimensional k E]
      [Algebra.IsSeparable k E],
      IrreducibleSpace (AlgebraicGeometry.Spec (CommRingCat.of (R ⊗[k] E)))) := by
  constructor
  · intro h E _ _ _ _
    exact h E
  · intro h L _ _
    have hsmall (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
        [Algebra.IsSeparable k E] : IrreducibleSpace (PrimeSpectrum (R ⊗[k] E)) := by
      have : Algebra.IsSeparable k (ULift.{max v w} E) :=
        AlgEquiv.Algebra.isSeparable (ULift.algEquiv (R := k)).symm
      have := h (ULift.{max v w} E)
      exact (PrimeSpectrum.homeomorphOfRingEquiv
        (TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R)
          (ULift.algEquiv (R := k))).toRingEquiv).irreducibleSpace_iff.mp this
    have hK := spec_tensor_separableClosure k R hsmall
    have : IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) :=
      (PrimeSpectrum.homeomorphOfRingEquiv
        (TensorProduct.comm k (SeparableClosure k) R).toRingEquiv).irreducibleSpace_iff.mpr hK
    obtain ⟨M, _, _, i, j, _, _⟩ :=
      Field.exists_common_extension k (SeparableClosure k) L
    let : Algebra (SeparableClosure k) M := i.toRingHom.toAlgebra
    have : IsScalarTower k (SeparableClosure k) M :=
      IsScalarTower.of_algebraMap_eq (fun x ↦ (i.commutes x).symm)
    have : IrreducibleSpace (AlgebraicGeometry.Spec (CommRingCat.of M)) :=
      PrimeSpectrum.irreducibleSpace
    have : IrreducibleSpace
        (AlgebraicGeometry.Spec (CommRingCat.of (SeparableClosure k ⊗[k] R))) :=
      ‹IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R))›
    have : IrreducibleSpace
        (PrimeSpectrum (M ⊗[SeparableClosure k] (SeparableClosure k ⊗[k] R))) :=
      IsSepClosed.irreducibleSpace_tensorProduct (SeparableClosure k) M
        (SeparableClosure k ⊗[k] R)
    have : IrreducibleSpace (PrimeSpectrum (M ⊗[k] R)) :=
      (PrimeSpectrum.homeomorphOfRingEquiv
        (TensorProduct.cancelBaseChange k (SeparableClosure k) M M R).toRingEquiv
          ).irreducibleSpace_iff.mp inferInstance
    let f : L ⊗[k] R →ₐ[k] M ⊗[k] R := TensorProduct.map j (AlgHom.id k R)
    have : IrreducibleSpace (PrimeSpectrum (L ⊗[k] R)) :=
      spec_irreducible_of_injective f.toRingHom
        (Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap j.injective)
    exact (PrimeSpectrum.homeomorphOfRingEquiv
      (TensorProduct.comm k R L).toRingEquiv).irreducibleSpace_iff.mpr inferInstance

end Algebra
