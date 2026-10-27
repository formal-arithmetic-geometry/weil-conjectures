## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_mvPolynomial_eulerChar_tensorPowers`
with a complete proof by induction on a natural bound for support dimension.
The existing public imports, signature, universes and integer-power list fold are unchanged.
The proof handles empty support separately, using the zero polynomial, and derives the
exact support-dimension bound from finite dimensionality of a proper scheme.

Added `Sheaf.Algebra.MvPolynomial.CoordinateDifferences`, with a complete proof of
`MvPolynomial.exists_eval_eq_of_coordinate_differences`. It integrates each polynomial
coordinate difference with zero value on the zero slice, proves constancy in the first
coordinate in both integer directions, and inducts on the remaining coordinates.
The antidifference and substitution degree bounds are proved explicitly. It uses the
already proved source-library univariate Newton theorem, rather than reproving it.

Added `Sheaf.AlgebraicGeometry.EulerTwistCoordinateDifference`, stating the genuinely
geometric dimension-drop step independently of any polynomial conclusion. Its coherent
modules and integer coefficients are chosen uniformly before all integer exponents.
The main proof applies dimension induction to those modules, forms a finite polynomial
linear combination, and invokes the proved arithmetic integration theorem.

All three delivery modules compile together with `lcompile.py --all`, without warnings.
No existing definition or theorem statement changes, and no consumer adaptation or change
record is required. No adopted source-library file was changed.

## Proved and sorry left

Original holes: one, in
`AlgebraicGeometry.Scheme.Modules.exists_mvPolynomial_eulerChar_tensorPowers`.
That body now contains no sorry and its combination of the lower statements is complete.

Added holes: one, in
`AlgebraicGeometry.Scheme.Modules.eulerChar_tensorPowers_coordinate_difference`
(node `lem-sc-euler-twist-coordinate-difference`). Its proof is exactly `by sorry`.
It has its own source, complete proof in words, and DAG node. There are no other retained
or added sorries. Thus this delivery is a decomposition (one upper hole closed and one
strictly geometric lower hole added), not a net closure of one hole.

The new arithmetic theorem
`MvPolynomial.exists_eval_eq_of_coordinate_differences` is proved with no sorry, as are
all its private helpers and the main module's four private helpers.
`#print axioms` for the arithmetic theorem reports exactly `propext`, `Classical.choice`
and `Quot.sound`. The retained
geometric lemma has no polynomial conclusion and does not assume a repackaged version
of Snapper's theorem. Its four lower-dimensional sheaves are the two pushed-forward
regular-section cokernels and the two embedded-kernel contributions.

Edge cases checked in the proofs: no variables; degree bound zero; zero difference
polynomials; negative integers in the integrated coordinate; empty support (dimension
bottom); and zero Euler characteristic. The remaining geometric statement also permits
the empty sum and zero cokernels. When support dimension is already at most d, its
conclusion follows using F tensor L_j and F themselves, without a dimension induction.

## No longer needed

Removed these direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.HilbertDifference`
- `Sheaf.AlgebraicGeometry.RegularMeromorphicSectionExists`
- `Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints`
- `Sheaf.Paper.SchemeTheoreticSupport`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`
- `WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport`

The geometric dependencies remain necessary for the retained geometric lemma, and its
node records them. The retired `Sheaf.Paper.SchemeTheoreticSupport` reexport is unnecessary;
the plan uses the canonical source-library statement. No claim is made that any of these
modules has become unreachable from all targets; none is withdrawn or deleted. No DAG
node is pruned. The unit's numerical-polynomial route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old third proof step proposed applying `hilbert_difference` to F already tensored by
the other variable powers. That produces cokernels depending on the other exponents;
it does not by itself supply fixed lower-dimensional modules to which multivariate
induction applies. The new geometric lemma records the required uniform conclusion.
Its proof plan chooses the two regular-section exact sequences for the untwisted
module first and then tensors both sequences by the entire product. The embedded-point
kernel contributes the two additional fixed modules K tensor L_j and K. The remaining
formal glue is isolated honestly in that lemma.

The source location in the original node says Tag 0BEL, whereas the theorem and its
proof are Tag 0BEM (Section 0BEL). No source field or mathematical statement was changed
in the existing node; the updated proof references use Tag 0BEM.

The source-library Hilbert polynomial theorem requires an ample invertible module and
natural powers. It cannot replace this statement about arbitrary invertible modules and
all integer powers. Its already proved finite-dimension and zero-Euler helpers are used.

## New nodes

`lem-sc-coordinate-differences-polynomial` attaches the fully proved integer-lattice
integration theorem in `Sheaf.Algebra.MvPolynomial.CoordinateDifferences`. Its dependency
on the existing univariate Newton theorem is recorded using
`lem-trf-rational-sequence-polynomial-forward-difference`, whose source-library declaration
is already proved. Natural-language, Loogle/LeanFinder, and Mathlib-source searches are
recorded; whole-blueprint searches found no duplicate of this multivariate result.

`lem-sc-euler-twist-coordinate-difference` attaches the geometric uniform dimension-drop
lemma in `Sheaf.AlgebraicGeometry.EulerTwistCoordinateDifference`. It records the original
embedded-point, support-equivalence, regular-section, Euler-additivity and closed-immersion
inputs. It is strictly the geometric part of Tag 0BEM, with no polynomial conclusion.
Its statement, source, detailed proof, searches and edge cases are supplied for the next
worker. Whole-blueprint and DAG searches found the existing narrower HilbertDifference
statement, which is cited rather than duplicated.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
