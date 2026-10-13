/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.FilteredCohomologyImage

/-! # Images and inverse images of filtered cycles in cohomology

Source: Stacks Project, Section 12.24, Equation 12.24.5.2 and Tag 012Q.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The class map from filtered cycles has the expected image and inverse image.
Source: Stacks Project, Section 12.24, Equation 12.24.5.2 and Tag 012Q.
(blueprint: new-cohomology-image-cycle-map).

Proof. Write A = L^pK^n, A' = L^(p+1)K^n, Z = ker(d^n), B = im(d^(n-1)),
and S = A intersection Z. Since the inclusion L^pK into K is degreewise monic,
its induced map on cycles identifies the cycles of L^pK with S: this follows
by taking the pullback of the outgoing differential kernel along the inclusion.
The equation c followed by the ambient cycle inclusion equals S.arrow identifies
c with this cycle map, after that identification, by uniqueness of kernel lifts.
Naturality of the cycle-to-homology projection and its epimorphy then show that
the image of c followed by homologyπ is the image of H^n(L^pK) in H^n(K).
This proves the first equality, and the same argument at p+1 identifies the next
image step with the image of A' intersection Z under the ambient class map.
The ambient class map Z onto H^n(K) is epic and has kernel B, viewed inside Z.
The inverse image of the image of A' intersection Z under this epimorphism is
B + (A' intersection Z). Restricting this subobject to S gives the inverse image
under c followed by homologyπ. The modular identity for subobjects gives
S intersection (B + (A' intersection Z)) =
(A intersection B) + (A' intersection Z), because B is contained in Z by d²=0
and A' is contained in A by antitonicity. Pulling back along S.arrow yields the
second equality. These are identities of constructed subobjects, requiring no
finiteness, stationarity or choice of an unproved witness.
-/
theorem cohomologyImage_cycle_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ)
    (c : ((L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ :
      Subobject (K.X n)) : C) ⟶
      K.cycles n)
    (hc : c ≫ K.iCycles n =
      (L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let f := c ≫ K.homologyπ n
  imageSubobject f = (L.cohomologyImage n).step p ∧
    (Subobject.pullback f).obj ((L.cohomologyImage n).step (p + 1)) =
      (Subobject.pullback (A ⊓ Z).arrow).obj ((A ⊓ B) ⊔ (A' ⊓ Z)) := by sorry

end CategoryTheory.DecreasingFiltration
