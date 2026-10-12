/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.Filtration

/-! # The normalized stationary quotient presentation

Source: Stacks Project, Tag 012Q, proof of the stationary-page formula.
(blueprint: lem-sp-filtered-normalized-quotient-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The quotient of normalized cycle and boundary subobjects has the cycle presentation.
Source: Stacks Project, Tag 012Q, final quotient calculation, Equation 12.24.5.2.
(blueprint: lem-sp-filtered-normalized-quotient-presentation).

Proof. Set A=L^pK^n, A'=L^(p+1)K^n, Z=ker(d^n), B=im(d^(n-1)).
The degree-n projection q from L^pK to gr^pK is an epimorphism whose kernel
is the degree-n image of L^(p+1)K. Evaluation preserves cokernels, so its
kernel inside A is the restriction of A'. The normalized cycle subobject
is the image of (A intersection Z)+A', restricted to A, under q; the
normalized boundary subobject is the image of (A intersection B)+A'.
Map A intersection Z onto the former, then onto its quotient by the latter.
This map is epic: adding A' does not change an image under q. Its kernel
is the restriction to A intersection Z of (A intersection B)+A'.
Since B is contained in Z by d squared equal to zero and A' is contained
in A by antitonicity, the modular identity identifies that kernel with
(A intersection B)+(A' intersection Z), restricted to A intersection Z.
The first isomorphism theorem gives the displayed cokernel isomorphism.
This calculation uses neither cohomology nor stationarity hypotheses.
-/
theorem normalizedStationaryQuotient_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  let P := Subobject.pullback ((L.step p).arrow.f n)
  let Zbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ Z) ⊔ A'))
  let Bbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ B) ⊔ A'))
  ∀ hBZ : Bbar ≤ Zbar,
    Nonempty (cokernel (Subobject.ofLE Bbar Zbar hBZ) ≅
      cokernel ((Subobject.pullback (A ⊓ Z).arrow).obj
        ((A ⊓ B) ⊔ (A' ⊓ Z))).arrow) := by sorry

end CategoryTheory.DecreasingFiltration
