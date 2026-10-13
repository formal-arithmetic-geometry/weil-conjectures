/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyCoupleData

/-!
# Exactness of the explicit filtered homology maps

Source: Stacks Project, Tags 012K and 011Q, the homology long exact sequence.
(blueprint: lem-sp-filtered-homology-couple-exactness).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- The explicitly constructed inclusion, connecting map, and projection are exact.
Source: Stacks Project, Tags 012K and 011Q; Mathlib HomologySequence.
(blueprint: lem-sp-filtered-homology-couple-exactness).

Proof. For each p the complex F^(p+1) -> F^p -> gr^p is short exact:
its first map is mono and the second is its cokernel projection. Apply its
long exact homology sequence. At p=-Q and degree P+Q, comp_delta and
homology_exact3 give the projection/connecting zero and exactness at E.
At p=-Q and degrees P+Q, P+Q+1, delta_comp and homology_exact1 give the
connecting/inclusion zero and exactness at the next D. At p=-(Q+1) and
degree P+Q, the zero composite of the two original complex maps and
homology_exact2 give the inclusion/projection zero and exactness at D.
The equalities -(Q-1)=-Q+1, -(Q+1)+1=-Q, P+2+(Q-1)=P+Q+1 and
P-1+(Q+1)=P+Q identify the indices. Transport each short complex by the
corresponding eqToIso; exactness is invariant under this isomorphism.
Convert its exactness to the imageSubobject=kernelSubobject equation.
This proves the six assertions for these maps without constructing or
comparing any derived page. -/
theorem filteredHomologyCouple_exact (C : Type u) [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    (∀ P Q, filteredHomologyF K F P Q ≫
      filteredHomologyAlpha K F (P + 2) (Q - 1) = 0) ∧
    (∀ P Q, filteredHomologyG K F P Q ≫
      filteredHomologyF K F (P + (0 : ℕ)) (Q - (0 : ℕ)) = 0) ∧
    (∀ P Q, filteredHomologyAlpha K F P Q ≫
      filteredHomologyG K F (P - 1) (Q + 1) = 0) ∧
    (∀ P Q, imageSubobject (filteredHomologyF K F P Q) =
      kernelSubobject (filteredHomologyAlpha K F (P + 2) (Q - 1))) ∧
    (∀ P Q, imageSubobject (filteredHomologyG K F P Q) =
      kernelSubobject (filteredHomologyF K F (P + (0 : ℕ)) (Q - (0 : ℕ)))) ∧
    (∀ P Q, imageSubobject (filteredHomologyAlpha K F P Q) =
      kernelSubobject (filteredHomologyG K F (P - 1) (Q + 1))) := by sorry

end CategoryTheory
