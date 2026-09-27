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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The trace on perfect complexes is the alternating sum of the traces

Let `R` be a commutative ring. A bounded complex `P` of finitely generated projective
`R`-modules is a dualizable object of the derived category `D(R)`, and the categorical
trace `CategoryTheory.MonoidalCategory.trace` of a chain endomorphism `v` of `P` is an
endomorphism of the unit object, i.e. an element of `R`. This file states that it is the
alternating sum `∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)` of the ordinary module traces of the
components of `v`.

## Main results

- `DerivedCategory.trace_eq_sum_negOnePow_trace`: the alternating sum formula (blueprint
  `sk-p-trace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]

/-- Blueprint `sk-p-trace`: Trace on perfect complexes.

For a commutative ring `R`, a bounded complex `P` of finitely generated projective
`R`-modules and a chain endomorphism `v : P ⟶ P`, the categorical trace of `v` on the object
of `D(R)` represented by `P` is the alternating sum of the ordinary `R`-module traces of the
components of `v`:

`tr_R (v ∣ P) = ∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)`.

Boundedness of `P` is rendered by a `Finset ℤ` containing its support, which also makes the
right hand sum finite. The sign `(-1) ^ i` of an integer exponent is `Int.negOnePow i`,
acting on `R` by `zsmul`.

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
  the sign `(-1) ^ i`, the dual of the degree `i` part having degree `-i`.
* Perfectness of `P` is rendered as an object `K` of `D(R)` with `[HasRightDual K]` together
  with an isomorphism `e : K ≅ Q.obj P` intertwining `w` and `Q.map v`, since this project
  has no `Perf R` and does not prove that a bounded complex of finitely generated
  projectives is dualizable. The categorical trace is conjugation invariant, so the choice of
  `e` does not matter.
* The identification `End (𝟙_ D(R)) = R` is an `R`-algebra isomorphism `ρ`, not merely a ring
  isomorphism: `End (𝟙_ D(R))` is an `R`-algebra because `D(R)` is `R`-linear, and an
  `R`-algebra isomorphism onto `R` is unique, whereas a bare ring isomorphism could be
  composed with a ring automorphism of `R` and would make the statement false. -/
theorem trace_eq_sum_negOnePow_trace
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i))
    (hproj : ∀ i, Module.Projective R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (K : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v)
    (ρ : End (𝟙_ (DerivedCategory (ModuleCat.{u} R))) ≃ₐ[R] R) :
    ρ (MonoidalCategory.trace w) =
      ∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom :=
  sorry

end DerivedCategory
