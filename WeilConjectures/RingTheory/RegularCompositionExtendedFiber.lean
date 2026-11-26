/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IsTensorProduct

/-!
# The map between extended fibres of a tower

For a tower `A → B → C` with `B → C` regular, the fibres of the induced map between finite
extensions of the fibres over a prime of `A` are regular.

## Implementation details

With `k = κ(p)` and `B_K = K ⊗_k (k ⊗_A B)`, tensor cancellation identifies the fibre at `q'`
with `κ(q') ⊗_{κ(q)} (κ(q) ⊗_B C)`. Since `B → B_K` is essentially of finite type, `κ(q')/κ(q)`
is finitely generated, and Lemma 0381 makes this tensor product of the geometrically regular
fibre regular. No regularity of `A → B` and no purely inseparable hypothesis on `K` are used.

## References

* [Stacks, Tag 07QI]
* [Stacks, Tag 0381]
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace RingHom

private theorem regular_fibre_baseChange
    {R : Type u} {S : Type v} {R' : Type w}
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    [Algebra.EssFiniteType R R'] (hf : (algebraMap R S).IsRegular)
    (q : Ideal R') [q.IsPrime] : IsRegularRing (q.Fiber (TensorProduct R R' S)) := by
  let p := q.comap (algebraMap R R')
  have : p.IsPrime := Ideal.comap_isPrime _ q
  have : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType p.ResidueField q.ResidueField := inferInstance
  rw [IsRegular, toAlgebra_algebraMap] at hf
  have : IsRegularRing (TensorProduct p.ResidueField q.ResidueField (p.Fiber S)) :=
    Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular (hf.2 p)
      q.ResidueField (IntermediateField.fg_top _ _)
  let e₁ := Algebra.TensorProduct.cancelBaseChange R p.ResidueField
    q.ResidueField q.ResidueField S
  have : IsRegularRing (TensorProduct R q.ResidueField S) :=
    IsRegularRing.of_ringEquiv e₁.toRingEquiv
  let e₂ := Algebra.TensorProduct.cancelBaseChange R R' q.ResidueField q.ResidueField S
  exact IsRegularRing.of_ringEquiv e₂.toRingEquiv.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A fibre of the map between finite extensions of the fibres of a tower is regular
when the upper map is regular. -/
theorem IsRegular.extendedFiber_regular
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hg : (algebraMap B C).IsRegular)
    (p : Ideal A) [p.IsPrime]
    (K : Type t) [Field K] [Algebra p.ResidueField K] [Module.Finite p.ResidueField K] :
    letI := (Algebra.TensorProduct.map (AlgHom.id p.ResidueField K)
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom A B C))).toRingHom.toAlgebra
    ∀ (q : Ideal (TensorProduct p.ResidueField K (p.Fiber B))) [q.IsPrime],
      IsRegularRing (q.Fiber (TensorProduct p.ResidueField K (p.Fiber C))) := by
  let X := p.Fiber B
  let Y := p.Fiber C
  let D := TensorProduct p.ResidueField K X
  let E := TensorProduct p.ResidueField K Y
  let f₁ := Algebra.TensorProduct.lTensor (S := p.ResidueField) p.ResidueField
    (IsScalarTower.toAlgHom A B C)
  let f₂ := Algebra.TensorProduct.lTensor (S := p.ResidueField) K f₁
  algebraize [f₁.toRingHom, f₂.toRingHom]
  let e₁ : Y ≃ₐ[X] X ⊗[B] C :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg A p.ResidueField B X C).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
        A B C p.ResidueField) x) }
  let e₂ : E ≃ₐ[D] D ⊗[X] Y :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg p.ResidueField K X D Y).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
        p.ResidueField X Y K) x) }
  let : Algebra B D := ((algebraMap X D).comp (algebraMap B X)).toAlgebra
  have : IsScalarTower B X D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : E ≃ₐ[D] D ⊗[B] C := e₂.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D) e₁).trans
      (Algebra.TensorProduct.cancelBaseChange B X D D C)
  intro q hq
  have : Algebra.EssFiniteType B X := by
    let e := Algebra.TensorProduct.commRight A B p.ResidueField
    exact Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  have : Algebra.EssFiniteType X D := by
    let e := Algebra.TensorProduct.commRight p.ResidueField X K
    exact Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  have : Algebra.EssFiniteType B D := Algebra.EssFiniteType.comp B X D
  have : IsRegularRing (q.Fiber (D ⊗[B] C)) := regular_fibre_baseChange hg q
  change IsRegularRing (TensorProduct D q.ResidueField E)
  exact IsRegularRing.of_ringEquiv (R := q.Fiber (D ⊗[B] C))
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : q.ResidueField ≃ₐ[q.ResidueField] q.ResidueField) e.symm).toRingEquiv

end RingHom
