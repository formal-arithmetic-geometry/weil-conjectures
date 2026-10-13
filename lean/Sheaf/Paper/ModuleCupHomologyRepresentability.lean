/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Homology represented by a single free module

Source: Stacks Project, Tag 064B (K-projective complexes), and Tag 068G.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The free rank-one module in degree n, also denoted k[-n]. -/
abbrev cupSingleModule (k : Type u) [CommRing k] (n : ℤ) :=
  (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
    (ModuleCat.of k k)

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- Homology represented by the shifted free module, with the cocycle normalization.
No representative or derived object is selected by this interface. -/
structure CupHomologyRepresentability where
  equiv : ∀ (A : DerivedCategory (ModuleCat.{u} k)) (n : ℤ),
    (DerivedCategory.Q.obj (cupSingleModule k n) ⟶ A) ≃ₗ[k]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj A
  natural : ∀ (A B : DerivedCategory (ModuleCat.{u} k)) (n : ℤ)
    (f : DerivedCategory.Q.obj (cupSingleModule k n) ⟶ A) (g : A ⟶ B),
    equiv B n (f ≫ g) = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map g
      (equiv A n f)
  on_cycles : ∀ (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (f : cupSingleModule k n ⟶ K) (z : K.cycles n),
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of k k)).inv ≫
      f.f n) (1 : k) = K.iCycles n z →
    equiv (DerivedCategory.Q.obj K) n (DerivedCategory.Q.map f) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv
        (K.homologyπ n z)

/-- Hom from k[-n] naturally identifies with H^n, including its value on cocycles.
Source: Stacks Project, Tag 064B, the K-projective localization description;
Tag 068G, representing a cohomology class by a cocycle.
(blueprint: lem-sc-module-cup-homology-representability)
Proof: the single complex k[-n] is bounded above and consists of projectives,
so it is K-projective. Morphisms from its localization to Q(K) are chain maps
modulo chain homotopy. A chain map is determined by the image of 1 in degree n,
which is a cycle, and a homotopy changes this image by a boundary. Thus evaluation
at 1 identifies the quotient with H^n(K), bijectively and k-linearly. Every derived
object has a representative, and the identification commutes with quasi-isomorphisms,
so it descends to every A. Postcomposition gives naturality. For a chain map f
with the displayed cycle z, evaluation is homology projection of z; transport by
homologyFunctorFactors gives exactly on_cycles. This works in every integer degree,
for unbounded K, the zero ring and zero cycles; no projectivity of K is required. -/
theorem exists_cupHomologyRepresentability : Nonempty (CupHomologyRepresentability k) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
