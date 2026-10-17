/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Integral closures in base changes of products

* `integralClosurePiEquiv`: the integral closure of `R` in a finite product `Π i, A i` is the
  product of the integral closures.
* `etale_integralClosure_tensorProduct_of_algEquiv`,
  `etale_integralClosure_tensorProduct_pi`: the property "the integral closure of `O₂` in
  `O₂ ⊗[O] L` is finite étale over `O₂`" is invariant under isomorphisms of `O`-algebras `L` and
  stable under finite products.
-/

@[expose] public section

open TensorProduct

/-- An element of a finite product of `R`-algebras is integral if all its components are. -/
theorem IsIntegral.of_pi {R ι : Type*} [CommRing R] [Finite ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {x : Π i, A i} (hx : ∀ i, IsIntegral R (x i)) :
    IsIntegral R x := by
  classical
  have := Fintype.ofFinite ι
  choose p hp hpx using hx
  refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ fun i _ ↦ hp i, ?_⟩
  funext j
  refine (Polynomial.aeval_algHom_apply (Pi.evalAlgHom R A j) x (∏ i, p i)).symm.trans ?_
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hpx j)

/-- The integral closure of `R` in a finite product of `R`-algebras is the product of the integral
closures. -/
noncomputable def integralClosurePiEquiv (R : Type*) {ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    integralClosure R (Π i, A i) ≃ₐ[R] Π i, integralClosure R (A i) :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ (Pi.evalAlgHom R A i).mapIntegralClosure)
    ⟨fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i)), fun y ↦
      ⟨⟨fun i ↦ (y i : A i), IsIntegral.of_pi fun i ↦ (y i).2⟩, rfl⟩⟩

/-- The property "the integral closure of `O₂` in `O₂ ⊗[O] L` is finite étale over `O₂`" is
invariant under isomorphisms of `O`-algebras `L`. -/
theorem etale_integralClosure_tensorProduct_of_algEquiv {O O₂ L L' : Type*} [CommRing O]
    [CommRing O₂] [Algebra O O₂] [CommRing L] [CommRing L'] [Algebra O L] [Algebra O L']
    (e : L ≃ₐ[O] L')
    (h : Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] L)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] L))) :
    Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] L')) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] L')) := by
  let E := (Algebra.TensorProduct.congr (AlgEquiv.refl : O₂ ≃ₐ[O₂] O₂) e).mapIntegralClosure
  have := h.1
  have := h.2
  exact ⟨.of_equiv E, .equiv E.toLinearEquiv⟩

/-- The property "the integral closure of `O₂` in `O₂ ⊗[O] L` is finite étale over `O₂`" is stable
under finite products. -/
theorem etale_integralClosure_tensorProduct_pi {O O₂ ι : Type*} [CommRing O] [CommRing O₂]
    [Algebra O O₂] [Finite ι] (L : ι → Type*) [∀ i, CommRing (L i)] [∀ i, Algebra O (L i)]
    (h : ∀ i, Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] L i)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] L i))) :
    Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] Π i, L i)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] Π i, L i)) := by
  classical
  have := Fintype.ofFinite ι
  have (i : ι) := (h i).1
  have (i : ι) := (h i).2
  let E := (Algebra.TensorProduct.piRight O O₂ O₂ L).mapIntegralClosure.trans
    (integralClosurePiEquiv O₂ fun i ↦ O₂ ⊗[O] L i)
  exact ⟨.of_equiv E.symm, .equiv E.symm.toLinearEquiv⟩
