/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.ModuleCupShiftedUnitTensor

/-! # Tensoring homology classes in the derived category of modules

Source: Stacks Project, Tags 0FKU and 068G.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type u} [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- The class of an integer-degree cycle, transported through the homology
factorization of localization. This uses only actual homology and an existing iso. -/
def cupLocalizedCycleClass (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (z : K.cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv
    (K.homologyπ n z)

/-- The natural tensor of derived homology classes, normalized on cochain cycles.
This is an interface, rather than a choice of an unproved operation. -/
structure CupDerivedHomologyTensor (k : Type u) [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)] where
  pair : ∀ (A B : DerivedCategory (ModuleCat.{u} k)) (p q : ℕ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj A →ₗ[k]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).obj B →ₗ[k]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).obj (A ⊗ B)
  natural : ∀ (A A' B B' : DerivedCategory (ModuleCat.{u} k))
    (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ)
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj A)
    (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).obj B),
    pair A' B' p q
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).map f a)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).map g b) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).map (f ⊗ₘ g)
        (pair A B p q a b)
  on_cycles : ∀ (K L : CochainComplex (ModuleCat.{u} k) ℤ) (p q : ℕ)
    (a : K.cycles p) (b : L.cycles q),
    ∃ z : (K ⊗ L).cycles (p + q),
      (K ⊗ L).iCycles (p + q) z =
        (HomologicalComplex.ιTensorObj K L p q (p + q) (by omega))
          ((K.iCycles p a) ⊗ₜ[k] (L.iCycles q b)) ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).map
          (Functor.LaxMonoidal.μ DerivedCategory.Q K L)
          (pair (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) p q
            (cupLocalizedCycleClass K p a) (cupLocalizedCycleClass L q b)) =
        cupLocalizedCycleClass (K ⊗ L) (p + q) z

/-- Derived homology admits its natural bilinear tensor pairing.
Source: Stacks Project, Tag 0FKU, global cohomology diagram following Lemma 20.31.3;
Tag 068G, tensor product of cocycles.
(blueprint: lem-sc-module-cup-derived-homology-tensor)
Proof: represent a class in H^p(A) by a morphism k[-p] to A. The rank-one free
module k is projective, so the standard homology/Hom identification is bijective.
Tensor the two representing morphisms and use the canonical identification
k[-p-q] with k[-p] tensor k[-q]. Transport back to homology. Additivity and
k-linearity of tensor give a bilinear map; composition gives naturality.
For localized complexes, the two representing maps are the single-complex maps
whose components are the supplied cocycles. Their tensor, followed by the lax
localization comparison, has component the indicated tensor summand. The signed
Leibniz rule says that component is a cycle. Applying homology gives on_cycles.
The same argument includes degree zero, zero complexes and zero
cycles; projectivity is used for the rank-one source, never for K or L. -/
theorem exists_cupDerivedHomologyTensor : Nonempty (CupDerivedHomologyTensor k) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
