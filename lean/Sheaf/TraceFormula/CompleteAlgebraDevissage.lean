/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Complete algebraic dévissage over a prime

Source: Stacks Project, flat.tex, Tag 05HX, definition-complete-devissage-algebra
(blueprint: def-trf-complete-algebra-devissage).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A complete dévissage of a finite module over a finite type algebra, over a prime.

Source: Stacks Project, Tag 05HX (blueprint: def-trf-complete-algebra-devissage).
This is the data and all eight conditions of the source.  The cokernel
of a map is represented by the quotient by its linear-map range; the base-change
condition is the bijectivity of the canonical tensor-product map.  Tensoring on the
left is equivalent, by tensor symmetry, to the source's tensoring on the right;
base change of the finite free module is canonically the free residue-field module.  The zero-length
case is represented by `n = 0` together with a subsingleton module. -/
structure CompleteAlgebraDevissage (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (r : Ideal R) [r.IsPrime]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N] where
  n : ℕ
  A : Fin n → CommAlgCat.{u} R
  B : Fin n → CommAlgCat.{u} R
  bToA : ∀ i, B i →ₐ[R] A i
  finiteA : ∀ i, (bToA i).toRingHom.Finite
  sToA : ∀ (i : Fin n), i.val = 0 → S →ₐ[R] A i
  sToA_surjective : ∀ (i : Fin n) (hi : i.val = 0), Function.Surjective (sToA i hi)
  sToA_finitePresentation : ∀ (i : Fin n) (hi : i.val = 0),
    (sToA i hi).toRingHom.FinitePresentation
  bToAnext : ∀ (i j : Fin n), j.val = i.val + 1 → B i →ₐ[R] A j
  bToAnext_surjective : ∀ (i j : Fin n) (hij : j.val = i.val + 1),
    Function.Surjective (bToAnext i j hij)
  bToAnext_finitePresentation : ∀ (i j : Fin n) (hij : j.val = i.val + 1),
    (bToAnext i j hij).toRingHom.FinitePresentation
  smooth : ∀ i, Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
  geometricallyIrreducible : ∀ i,
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
  pPrime : ∀ i, (Ideal.map (algebraMap R (B i)) r).IsPrime
  rIndex : Fin n → ℕ
  M : ∀ i, ModuleCat.{v} (A i)
  finiteM : ∀ i, Module.Finite (A i) (M i)
  alpha : ∀ i, (Fin (rIndex i) → B i) →ₗ[B i]
    (ModuleCat.restrictScalars (bToA i).toRingHom).obj (M i)
  residue_bijective : ∀ (i : Fin n) [_hp : (Ideal.map (algebraMap R (B i)) r).IsPrime],
    Function.Bijective
      (LinearMap.lTensor (Ideal.ResidueField (Ideal.map (algebraMap R (B i)) r)) (alpha i))
  firstIso : ∀ (i : Fin n) (hi : i.val = 0),
    N ≃ₗ[S] (ModuleCat.restrictScalars (sToA i hi).toRingHom).obj (M i)
  cokerIso : ∀ (i j : Fin n) (hij : j.val = i.val + 1),
    ((ModuleCat.restrictScalars (bToA i).toRingHom).obj (M i) ⧸ LinearMap.range (alpha i))
      ≃ₗ[B i] (ModuleCat.restrictScalars (bToAnext i j hij).toRingHom).obj (M j)
  last_zero : ∀ (i : Fin n), i.val + 1 = n →
    Subsingleton
      ((ModuleCat.restrictScalars (bToA i).toRingHom).obj (M i) ⧸ LinearMap.range (alpha i))
  zero_case : n = 0 → Subsingleton N

end AlgebraicGeometry
