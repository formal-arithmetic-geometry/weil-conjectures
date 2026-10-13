/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Assembling scalar cone coordinates into a complex isomorphism

Source: Stacks Project, More on Algebra, Tags 0628 and 0629, and
Homological Algebra, the definition of a mapping cone.
(blueprint: lem-pc-chain-cone-coordinates-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ChainComplex

/-- Degreewise scalar-cone coordinates compatible with the differentials assemble
into an isomorphism after extension from homological degree `n` to cochain degree `-n`.
Source: Stacks Project, Tags 0628 and 0629; the matrix of the cone differential.
(blueprint: lem-pc-chain-cone-coordinates-iso).

Proof: In cochain degree `-(n+1)`, use `e n` followed by the exchange of the two
factors to identify `K_(n+1)` with `L_n ⊕ L_(n+1)`. These are the source-shift
and target summands of the mapping cone. In degree zero use `e₀` and the
canonical identification of the cone with `L_0`, since the extended `L` in cochain degree
one is zero. In strictly positive cochain degrees both complexes are zero;
use the unique isomorphism between zero objects. In negative degrees the
higher differential equation gives, in this summand order, the matrix
`(y,x) ↦ (-d y, d x + a • y)`, exactly Mathlib's cone differential. The
separate degree-one equation verifies the differential into cochain degree
zero. The differential out of degree zero is zero on both sides. These checks
show that the degreewise isomorphisms commute with every differential.
Apply `HomologicalComplex.Hom.isoOfComponents`. No regularity or nonzero
hypothesis is used; this includes zero modules, the zero ring, and zero scalars. -/
theorem scalarCone_iso_of_coordinates (A : Type u) [CommRing A]
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) (a : A)
    (e₀ : K.X 0 ≃ₗ[A] L.X 0)
    (e : ∀ n : ℕ, K.X (n + 1) ≃ₗ[A] L.X (n + 1) × L.X n)
    (h₀ : ∀ x : K.X 1, e₀ (K.d 1 0 x) =
      L.d 1 0 (e 0 x).1 + a • (e 0 x).2)
    (hd : ∀ (n : ℕ) (x : K.X (n + 2)), e n (K.d (n + 2) (n + 1) x) =
      (L.d (n + 2) (n + 1) (e (n + 1) x).1 + a • (e (n + 1) x).2,
        -L.d (n + 1) n (e (n + 1) x).2)) :
    Nonempty (K.extend ComplexShape.embeddingDownNat ≅
      CochainComplex.mappingCone
        (a • 𝟙 (L.extend ComplexShape.embeddingDownNat))) := by sorry

end ChainComplex
