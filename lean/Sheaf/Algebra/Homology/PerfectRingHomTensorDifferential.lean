/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees

/-! # Differential compatibility of signed tensor-dual evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
chain-level calculation in `lem-pc-perfect-ring-hom-tensor-dual-iso`, step 2.
(blueprint: lem-pc-perfect-ring-hom-tensor-differential)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

/-- Any family with the signed evaluation formula commutes with the differentials.
There are no boundedness, projectivity, finiteness, or invertibility assumptions.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
chain-level calculation in `lem-pc-perfect-ring-hom-tensor-dual-iso`, step 2.
(blueprint: lem-pc-perfect-ring-hom-tensor-differential)

Proof: test equality after every tensor coproduct inclusion and every Hom product
projection. On the bottom-topology one-object site sheafification is invertible and
restriction maps in the unique slice are identities, so equality is detected on pure
tensors lam tensor y and vectors x. For a summand of bidegree (r,s), n=r+s, the tensor
differential has terms d_D(lam) tensor y and (-1)^r lam tensor d_Q(y). Since D is
Hom(P,A[0]), its differential on a functional is -(-1)^r lam composed with d_P.
For the second term the normalization in degree n+1 contributes (-1)^(r*(s+1));
combined with (-1)^r this is (-1)^(r*s), exactly the postcomposition term of the Hom
differential. For the first term the sign is -(-1)^(r+(r+1)*s), which equals
-(-1)^(r+s+r*s), exactly its precomposition term. The postcomposition term is supported
only in Hom coordinate -r and the precomposition term only in coordinate -r-1; all
other coordinates vanish by the off-diagonal condition. Degree transports agree by
proof irrelevance and naturality. Bilinearity extends the equality from pure tensors,
the sheafification adjunction gives equality on each sheaf tensor, and the coproduct
and product universal properties give the asserted equality. No finite-support
argument is used; zero objects, arbitrary unbounded Q, and the zero ring obey the
same equations. -/
theorem perfectRingHom_tensorDual_degree_comm {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (f : ∀ n : ℤ,
      (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n),
      (∀ n : ℤ, PerfectRingHomTensorDegreeCondition P Q n (f n)) →
      ∀ n m : ℤ, (ComplexShape.up ℤ).Rel n m →
        f n ≫ (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).d n m =
          (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).d n m ≫
            f m := by sorry

end CategoryTheory
