/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Right shifts of the Hom complex
Source: Stacks Project, Cohomology on Sites, Sections 21.34--21.35.
(blueprint: lem-pur-hom-complex-shift-right).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- The Hom-complex bifunctor commutes with shifts in its second complex.
Source: Stacks Project, sites-cohomology.tex, Sections 21.34 and 21.35
(Tags 0A8X and 08JA).
(blueprint: lem-pur-hom-complex-shift-right).
Proof: In degree k both sides are products indexed by p of internal Hom from
L^p to M^(p+k+n). Use the product universal property and the shift degree
isomorphisms to identify these products. The inverse uses the inverse degree
isomorphisms. The shifted differential has postcomposition coefficient
(-1)^n and precomposition coefficient -(-1)^(k+n+n) = -(-1)^k;
the Hom differential with shifted target has precisely these coefficients.
The product projections therefore verify the chain-map equation, and the
inverse equations hold projectionwise. Precomposition in L and postcomposition
in M commute with the degree identifications, giving naturality in both complexes.
The formula works for all integer shifts, unbounded complexes, and zero objects. -/
theorem homComplex_shift_right
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (n : ℤ) :
    Nonempty (
      Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R)) ⋙
        shiftFunctor _ n ≅
      (𝟭 _).prod (shiftFunctor _ n) ⋙
        Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R))) := by sorry

end CategoryTheory
