## What changed

Completed `AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange` in
`Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange`, with its existing signature.
For each degree n, upper truncation makes the input bounded and preserves allowable
cohomology. Apply the existing bounded allowable-torsion theorem. The new proved private
helper `truncation_homology_isIso` applies the long exact cohomology sequence to a mapped
standard truncation triangle: preservation of lower bounds kills the upper tail in
degrees n-1 and n. Apply this helper to both composites occurring in the canonical
exchange. Naturality and cancellation of isomorphisms prove that exchange is invertible
on every cohomology sheaf. `DerivedCategory.isIso_iff` gives the ambient isomorphism.
The existing direct-image and inverse-image preservation proofs give source membership;
strict fullness transports it to the target.

Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` for
shift compatibility and triangulatedness of total right derived direct image.
Local instances for allowable-torsion sheaves containing zero and being closed under
isomorphisms make upper truncation's property explicit. No definition, public signature,
public import, or other module is changed. The node's proof and dependencies now record
the actual direct truncation-triangle route. The unit `sk-rem-rest` has no realized steps;
the bounded-to-bounded-below argument of the source is retained, including n below the
chosen lower bound, when the upper truncation is zero.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange`
(node `sbc-thm-bounded-below-derived-smooth-base-change`).
Added zero holes; zero holes remain in the item. No statement was split off.
The private helper `truncation_homology_isIso` is completely proved.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion`, and removed
`sbc-lem-bounded-below-truncation-criterion` from this node's proof dependencies.
The proof only needs the two degree-n isomorphisms, each proved directly from the
standard triangle and lower-bound preservation; it does not need the criterion's
additional spectral-sequence support assertion. This does not withdraw the criterion
module or claim that its other consumers no longer need it.

Removed the node's obsolete direct tool approvals:
`sbc-lem-bc-naturality` (use the canonical transformation's own naturality),
`lem-weil-pbc-derived-stalk-conservative` (use `DerivedCategory.isIso_iff`),
`lem-weil-pbc-geometric-point-pullback-stalk` (the shared proved
`allowable_upperStar` supplies inverse-image torsion preservation),
`lemma-weil-pbc-direct-image-filtered-colimit` (the existing qcqs prime-torsion theorem
supplies the required sheaf result), and
`prop-weil-pbc-inverse-image-exact` (use the existing exact inverse-image functor's
cohomology and lower-bound API). The underlying shared results may still have consumers;
these are removals of direct tools from this node, not global withdrawal claims.
No further imports or proof dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG records `boundedBelow_truncation_criterion` as available, but its declaration is
commented out in the current module after the upstream sync. Its former import also
supplied derived triangulatedness indirectly. The direct standard-triangle argument
above resolves precisely the needed comparison without restoring the stronger
spectral-sequence theorem or changing another group's work. The existing public target
statement and the allowable-torsion output assertions are preserved.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
