/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.PerfectRingDualTermFlat

/-! # Existence of the signed degreewise evaluation map

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-map)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

/-- Signed evaluation defines a map in each degree, without finiteness assumptions.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-map)

Proof: use the product projections of Hom(P,A[0]) to evaluate its degree-r sections
on P^(-r), followed by the degree-zero single-complex identification with A.
Multiplication on Q^s gives an A-bilinear pairing, hence a map from the sectionwise
tensor. This pairing is natural under restriction. By the sheafification adjunction
it descends to the sheaf tensor. For r+s=n, put this signed map in Hom coordinate
p=-r, transporting Q^s to Q^(p+n), and put zero in every other coordinate.
The product universal property gives a map from this tensor summand to Hom degree n.
The coproduct universal property defining the total tensor degree assembles all
summands. Its composites with projections vanish off the diagonal by construction;
on the diagonal its value on pure tensors is precisely the defining signed pairing.
The argument uses no bound, finite generation, or projectivity. Zero modules and the
zero ring are included because the bilinear pairing and both universal properties
still apply. -/
theorem perfectRingHom_tensorDual_degree_map_exists {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∃ f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n,
      PerfectRingHomTensorDegreeCondition P Q n f := by sorry

end CategoryTheory
