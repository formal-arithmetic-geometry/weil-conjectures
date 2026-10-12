/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersection
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.MvPolynomial.Rename
import Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
import Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
import Sheaf.Topology.DimensionSupremumLocalDimensions
import Sheaf.RingTheory.EquationCountLocalizePresentation
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Choosing a localization with the expected fibre dimensions

Source: Stacks Project, Algebra, Lemma 00ST (3), using 00QH and 0B7I.
-/

@[expose] public section

universe u

namespace Algebra

/-- There is a polynomial avoiding q whose enlarged quotient has the expected fibre dimensions.
Source: Stacks Project, Algebra, Lemma 00ST (3), proof via 00QH, and dimension formula 0B7I.
(blueprint: new-equation-count-localize-rgci).

Proof: the finite polynomial quotient S is finite type over R. Apply 00QH at q to find
an open neighbourhood V where each point has local fibre dimension at most n-c. Since basic
opens form a basis, choose g avoiding q with D(g) contained in V, and lift g to a polynomial h
using quotient surjectivity. Over a residue field, the fibre of S is a polynomial quotient
by c equations in n variables. The polynomial quotient dimension formula and Krull's height
bound imply local dimension at least n-c at each point. The fibre of S_g is the principal
open defined by g in the corresponding fibre of S, and dimension at a point is unchanged
on an open subspace. Thus all points of each fibre of S_g have local dimension exactly n-c.
The inverse-variable presentation identifies T with S_g, and base change transports this
identification to every fibre. For a nonzero fibre the spectrum is nonempty; its dimension
is the supremum of its local dimensions (0B7I), hence n-c. The count for the displayed
presentation is (n+1)-(c+1)=n-c, and c+1 ≤ n+1 follows from c ≤ n. Reindex the Option variables
and equations by Fin (n+1) and Fin (c+1), using their standard equivalences. The quotient
isomorphism under this reindexing and the fibre dimensions provide the existential finite
presentation in the definition of IsRelativeGlobalCompleteIntersection. -/
theorem localized_presentation_is_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hdim : let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let p := PrimeSpectrum.comap (algebraMap R S) q
      c ≤ n ∧ topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩) = (n - c : ℕ))
    : ∃ h : MvPolynomial (Fin n) R,
    let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
    let g : S := Ideal.Quotient.mk _ h
    g ∉ q.asIdeal ∧
    let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
      Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
        (fun i ↦ MvPolynomial.rename some (f i))
    let T := MvPolynomial (Option (Fin n)) R ⧸ Ideal.span (Set.range relations)
    IsRelativeGlobalCompleteIntersection (algebraMap R T) ∧
      (∀ (p : Ideal R) (_hp : p.IsPrime),
        letI : p.IsPrime := _hp
        Nontrivial (p.Fiber T) →
          c + 1 ≤ n + 1 ∧
            topologicalKrullDim (PrimeSpectrum (p.Fiber T)) =
              (n + 1 - (c + 1) : ℕ)) := by
  sorry

end Algebra
