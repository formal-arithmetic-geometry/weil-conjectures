/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.GaloisLisseRepresentationData
import Sheaf.Paper.LisseTensorScalarExtension

/-! # GaloisLisseFiniteCompatibility

Source: the proof of `cor-galois-lisse-representations`. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Tensor, unit and coefficient compatibility of the finite evaluation equivalence.
Source: blueprint `cor-galois-lisse-representations`, proof steps 3-5;
Stacks Project, Tag 0DV5 (3).
Proof: put the sheaf tensor product and constant unit on the lisse subcategory.
The stalk tensor comparison is equivariant: apply naturality of gamma to the
bilinear map of underlying finite locally constant sheaves; it sends pure
tensors to the diagonal action. This lifts the canonical braided constraints.
Every element of a constant stalk is the germ of a constant global section;
naturality with its map from the terminal sheaf shows that gamma fixes it.
This proves the unit statement also for noncommutative finite rings.
Restrict sheafified balanced scalar extension to lisse objects. For a coefficient
b, naturality of gamma for z mapped to b tensor z makes its stalk comparison
equivariant. Lift this comparison through the fully faithful equivalence.
For composites, use the sheaf and module scalar-extension associators; both paths
on pure germs send b tensor (a tensor z) to b*g(a) tensor z. These generate
after sheafification, and equivalence faithfulness proves the compatibility.
(blueprint: lem-pod-galois-lisse-finite-compatibility). -/
theorem galois_lisse_finite_compatibility
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) (h : galoisFiniteEvaluationAction y G d) :
    galoisFiniteUnit y G d ∧ galoisFiniteTensor y G d ∧
      galoisFiniteScalarExtension y G d := by sorry

end AlgebraicGeometry.Scheme
