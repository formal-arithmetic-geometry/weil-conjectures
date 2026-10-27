/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# First cotangent homology of directed unions

Source: Stacks Project, Algebra, Tag 07BQ (lemma-colimits-NL), specialized to a
constant base and directed inclusions (blueprint: lem-sfb-directed-union-cotangent-h1).

`Algebra.H1Cotangent R D` is the kernel for the canonical evaluation presentation
`MvPolynomial D R → D`. The transition maps below use precisely these presentations;
the explicitly supplied algebra structure between two stages is their inclusion.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Classes in first cotangent homology descend to a member of a directed union,
and a class that becomes zero vanishes in a member containing its original stage.

Source: Stacks Project, Algebra, Tag 07BQ (lemma-colimits-NL), with the canonical
maps of Tag 00S1 (lemma-NL-homotopy)
(blueprint: lem-sfb-directed-union-cotangent-h1).

Proof:
1. The variable inclusion from the polynomial ring on a subalgebra into the
polynomial ring on `S` is injective and commutes with evaluation. Every finite
family of polynomials therefore lifts to one stage, by finite variable support
and directedness; nonemptiness covers the empty support. A prescribed stage can
also be included by taking a common upper member. This uses
`def-weil-pbc-mv-polynomial-ring` and does not require `R → S` to be injective.
2. By `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`, the differential
of a polynomial has coordinates its evaluated partial derivatives. Renaming
variables commutes with these derivatives on old labels and gives zero on new
labels. The coefficient identities commute with the injective subalgebra maps.
3. Represent a class over `S` by a polynomial in the evaluation kernel and lift
it to a stage using step 1. Its evaluated derivatives vanish at that stage by
step 2 and injectivity into `S`. Thus its conormal class lies in the differential
kernel. The representative formula of
`lem-weil-pbc-nl-presentation-h1-functoriality` identifies its image with the given
class, proving the first clause.
4. Represent a class at an initial stage whose image is zero by a polynomial
whose image belongs to the square of the evaluation kernel. Write that image
as a finite sum of products of kernel polynomials, absorbing any polynomial
coefficients into the factors. Lift all factors to a common stage containing
the initial one. Evaluation reflects their kernel membership; injectivity of
variable inclusion reflects the polynomial identity. Hence the representative
at this later stage belongs to the square of its evaluation kernel, so its
conormal class and its first homology class vanish. Presentation functoriality
identifies this class with the stipulated transition map. Empty sums are allowed.
-/
theorem H1Cotangent.directed_union
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (ι : Type w) [Nonempty ι] (A : ι → Subalgebra R S)
    (hdir : Directed (· ≤ ·) A) (hunion : ∀ s : S, ∃ i : ι, s ∈ A i) :
    (∀ h : H1Cotangent R S, ∃ (i : ι) (hᵢ : H1Cotangent R (A i)),
      H1Cotangent.map R R (A i) S hᵢ = h) ∧
    (∀ (i : ι) (h : H1Cotangent R (A i)),
      H1Cotangent.map R R (A i) S h = 0 →
      ∃ (j : ι) (hij : A i ≤ A j),
        @H1Cotangent.map R R _ _ _ (A i) _ _ (A j) _ _ _ _
          (Subalgebra.inclusion hij).toRingHom.toAlgebra
          (@IsScalarTower.of_algebraMap_eq' R (A i) (A j) _ _ _ _
            (Subalgebra.inclusion hij).toRingHom.toAlgebra _
            (Subalgebra.inclusion hij).comp_algebraMap.symm) h = 0) := by
  sorry

end Algebra
