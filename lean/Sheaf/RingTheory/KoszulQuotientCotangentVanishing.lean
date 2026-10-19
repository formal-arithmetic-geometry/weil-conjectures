/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.RingTheory.KoszulConormalBasis
import Sheaf.RingTheory.KoszulDerivedQuotient
import Sheaf.RingTheory.CotangentFlatBaseChange

/-!
# The cotangent complex of a Koszul-regular quotient

Source: Stacks Project, Cotangent Complex, Tag 08SJ (lemma-mod-regular-sequence),
with the canonical conormal identification of lemma-surjection
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing).

The module `I.Cotangent` is Mathlib's `I/I²`. Its single complex in degree `-1`
is `(I/I²)[1]`. The isomorphism is normalized on standard-resolution relation
cycles, so the conclusion specifies the canonical conormal identification.

## Main declarations

* `quotientArrow`, `quotientModel`: the quotient and its recorded standard complex.
* `relationVector`, `conormalHomologyMap`: the explicit conormal normalization.
* `exists_canonical_iso_and_vanishing`: the canonical isomorphism and vanishing.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Algebra.CotangentResolution

namespace Algebra.KoszulQuotientCotangent

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The quotient ring map as an arrow of commutative rings. Source: Stacks,
Tag 08SJ (blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def quotientArrow (R : Type u) [CommRing R] (I : Ideal R) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The standard differential complex computing the quotient's cotangent complex.
Source: Stacks, Tags 08PN and 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def quotientModel (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R) :=
  differentialComplex (C.differentials (C.standard (quotientArrow R I)))

/-- The relation vector `1 ⊗ d([C(a)] - [0])` in degree `-1` of the actual standard
resolution. Its two faces have zero differential for `a ∈ I`: the first evaluates
it to the base constant `a`, and the second to `[a mod I] - [0] = 0`.
It represents the conormal class of `a`. The cast uses the recorded equality
of the standard resolution's rings with the prescribed polynomial rings.
Source: Stacks, lemma-surjection, equation-comparison-map, and Tag 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def relationVector (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R)
    (a : I) : (quotientModel C R I).X (-1) :=
  complexGenerator (C.differentials (C.standard (quotientArrow R I))) 1 1
    (_root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
      ((C.standard_spec (quotientArrow R I)).1 1).symm)
      (MvPolynomial.X (MvPolynomial.C (a : R)) -
        MvPolynomial.X (MvPolynomial.C (0 : R))))

/-- The map on degree `-1` cohomology of a proposed conormal isomorphism, expressed
on the concrete standard complex using the localization and single-complex
comparison isomorphisms. Source: Stacks, lemma-surjection and Tag 08SJ
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing). -/
def conormalHomologyMap (C : Coherence.{u}) (R : Type u) [CommRing R] (I : Ideal R)
    (e : cotangentComplex C (quotientArrow R I) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).obj
        (ModuleCat.of (R ⧸ I) I.Cotangent)) :
    (quotientModel C R I).homology (-1) ⟶ ModuleCat.of (R ⧸ I) I.Cotangent :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).inv.app
      (quotientModel C R I) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).map e.hom ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (CommRingCat.of (R ⧸ I))) (-1)).hom.app (ModuleCat.of (R ⧸ I) I.Cotangent)

/-- A Koszul-regular quotient has cotangent complex canonically `I/I²[1]`, and
cohomology zero in every degree other than `-1`, without a Noetherian assumption.
The normalization sends the class of `1 ⊗ d([C(a)] - [0])` to `a mod I²` for every
`a ∈ I`; it also asserts that each displayed relation vector is a cycle.
Source: Stacks, Tag 08SJ, with lemma-surjection for the conormal normalization
(blueprint: lem-trf-koszul-quotient-cotangent-vanishing).

Proof:
1. Set `P = ℤ[x₁,…,xᵣ]`, sending `xᵢ` to `fᵢ`. Its variable Koszul complex is
   a free resolution of `ℤ`. By lem-trf-koszul-derived-quotient the canonical
   augmentation identifies `R ⊗ᴸ[P] ℤ` with `(R/I)[0]`, including `r = 0`.
2. Apply lem-trf-cotangent-flat-base-change to the square `(P,ℤ,R,R/I)`.
   Its precise hypothesis is the canonical derived-tensor isomorphism in (1),
   not flatness of `P → R`. Use lem-trf-cotangent-resolution-coherence for the
   standard complexes, square maps and comparisons in the ordinary module categories.
3. By lem-trf-cotangent-polynomial-special-case, `L_{ℤ/P} = (J/J²)[1]`.
   This conormal module has free basis `[xᵢ]`, so its derived tensor with `R/I`
   is the ordinary tensor placed in degree `-1`. The conormal base-change map
   sends `[xᵢ] ⊗ 1` to `[fᵢ]`; these form a basis by lem-sc-koszul-conormal-basis.
   Compose this isomorphism with the inverse of the base-change isomorphism.
   The conormal comparison of lemma-surjection sends a standard relation with
   first face `a` and second face zero to `[a]`. In the displayed standard model
   that relation is `[C(a)] - [0]`; taking differentials gives relationVector.
   Thus the composite has exactly the asserted normalization on every `a ∈ I`.
4. A module placed in degree `-1` has zero cohomology in all other degrees.
   Transport this through the isomorphism. For the empty sequence `I = 0` and
   `L_{R/R} = 0`; the zero ring and the unit ideal cause no exception. -/
theorem exists_canonical_iso_and_vanishing (C : Coherence.{u})
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    (∃ e : cotangentComplex C (quotientArrow R (Ideal.span (Set.range f))) ≅
        (DerivedCategory.singleFunctor
          (ModuleCat.{u} (CommRingCat.of (R ⧸ Ideal.span (Set.range f)))) (-1)).obj
            (ModuleCat.of (R ⧸ Ideal.span (Set.range f))
              (Ideal.span (Set.range f)).Cotangent),
      ∀ a : Ideal.span (Set.range f),
        ∃ z : (quotientModel C R (Ideal.span (Set.range f))).cycles (-1),
          (quotientModel C R (Ideal.span (Set.range f))).iCycles (-1) z =
              relationVector C R (Ideal.span (Set.range f)) a ∧
            conormalHomologyMap C R (Ideal.span (Set.range f)) e
              ((quotientModel C R (Ideal.span (Set.range f))).homologyπ (-1) z) =
                (Ideal.span (Set.range f)).toCotangent a) ∧
      ∀ i : ℤ, i ≠ -1 → IsZero
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (CommRingCat.of (R ⧸ Ideal.span (Set.range f)))) i).obj
            (cotangentComplex C (quotientArrow R (Ideal.span (Set.range f))))) := by
  sorry

end Algebra.KoszulQuotientCotangent
