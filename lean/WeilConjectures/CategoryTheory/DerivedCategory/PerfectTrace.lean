/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The trace on perfect complexes is the alternating sum of the traces

Let `R` be a commutative ring. A bounded complex `P` of finitely generated free `R`-modules
is a dualizable object of the derived category `D(R)`, and the categorical trace
`CategoryTheory.MonoidalCategory.trace` of a chain endomorphism `v` of `P` is an
endomorphism of the unit object, i.e. an element of `R`. This file states that it is the
alternating sum `∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)` of the ordinary module traces of the
components of `v`.

## Main results

- `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`: the alternating sum
  formula.

## Implementation notes

Four things are hypotheses rather than instances, because this project does not construct
them.

* `Abelian.HasFunctorialFlatResolution (ModuleCat R)` is assumed only so that the monoidal
  structure on `DerivedCategory (ModuleCat R)` is available, and is *the* derived tensor
  product `- ⊗ᴸ_R -` supplied by
  `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`, rather than an
  arbitrary one. Without it the statement would be about an unspecified tensor product.
* `BraidedCategory (DerivedCategory (ModuleCat R))` is assumed because no braiding on a
  derived category is constructed here, while `MonoidalCategory.trace` needs one. The
  intended braiding is the Koszul symmetry inherited from `ModuleCat R`; it is what produces
  the sign `(-1) ^ i`, the dual of the degree `i` part having degree `-i`. For the unsigned
  braiding the statement is false (`P = R[-1]`, `v = 𝟙` gives `+1 ≠ -1`), so the hypothesis
  `hβ` pins the Koszul sign: the braiding of `R[1]` with itself is `-1`.
* Perfectness of `P` is rendered as an object `K` of `D(R)` with `[HasRightDual K]` together
  with an isomorphism `e : K ≅ Q.obj P` intertwining `w` and `Q.map v`, since this project
  has no `Perf R` and does not prove that a bounded complex of finitely generated free
  modules is dualizable. The categorical trace is conjugation invariant, so the choice of
  `e` does not matter.
* The components of `P` are assumed `Module.Free`, not merely `Module.Projective`:
  Mathlib's `LinearMap.trace R M` is defined to be `0` unless `M` has a finite basis, so
  over a ring with a non-free finitely generated projective module the projective form of
  the statement is false.

The right hand side is an element of `R`, read in `End (𝟙_ D(R))` through the canonical
`R`-algebra structure that `R`-linearity of `D(R)` puts on it; no choice of an isomorphism
`End (𝟙_ D(R)) ≃ R` is needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]

/-- For a commutative ring `R`, a bounded complex `P` of finitely generated free `R`-modules
and a chain endomorphism `v : P ⟶ P`, the categorical trace of `v` on the object of `D(R)`
represented by `P` is the alternating sum of the ordinary `R`-module traces of the
components of `v`:

`tr_R (v ∣ P) = ∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)`.

Boundedness of `P` is rendered by a `Finset ℤ` containing its support, which also makes the
right hand sum finite. The sign `(-1) ^ i` of an integer exponent is `Int.negOnePow i`,
acting on `R` by `zsmul`. The braiding is the Koszul one in the sense that the braiding of
`R[1]` with itself is `-1` (blueprint: `sk-p-trace`). -/
theorem trace_eq_algebraMap_sum_negOnePow_linearMapTrace
    (hβ : (β_ ((𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦(1 : ℤ)⟧)
      ((𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦(1 : ℤ)⟧)).hom = -𝟙 _)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (K : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v) :
    MonoidalCategory.trace w =
      algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))
        (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom) :=
  sorry

end DerivedCategory
