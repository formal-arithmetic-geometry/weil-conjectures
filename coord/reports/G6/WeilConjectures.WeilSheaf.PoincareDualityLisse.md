## What changed

Proved `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
in `WeilConjectures.WeilSheaf.PoincareDualityLisse`, preserving its signature, attributes,
public imports and existing docstrings verbatim.

Added private proof imports of `Mathlib.LinearAlgebra.Dual.Lemmas`,
`WeilConjectures.WeilSheaf.VerdierDualFinite` and
`WeilConjectures.WeilSheaf.StalkRationalPoint`. The first supplies reflexivity of the
finite-dimensional cohomology space; the others supply smooth Verdier duality, point
cohomology duality and the identification of point global sections with a stalk.

The proof follows the unit's derived-duality-to-degreewise-duality argument in the native
Weil-complex API. Smooth purity identifies the Verdier dual of F with F-dual(d)[2d].
Verdier exchange identifies its ordinary image with the Verdier dual of the compact image.
The three proved private helpers compute cohomology of the latter dual at the point:
shift to the existing degree-minus-one truncation calculation, identify the dual of a
point sheaf with its coefficient dual, and identify the resulting global sections with
the linear dual. Their proofs reuse the already proved private point-duality argument
preserved in `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse`.
All these equivalences preserve Frobenius. Transporting the perfect evaluation pairing
therefore gives both required conclusions, with the complementary-degree equation used
explicitly to reindex the shift.

Validation: lcompile.py compiled the complete module without errors or warnings in
13.4 seconds. No definition, instance, public declaration signature or consumer changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
(the lisse Weil-sheaf realization of `thm-pod-degreewise-perfectness-over-a-field`, including
Frobenius invariance as in `thm-pod-equivariance-of-the-twisted-pairing`).

Added 0 holes. There are no remaining sorry proofs in the delivered module. All three
private helpers are proved. Existing imported obligations in WeilSheaf.VerdierDual
remain existing obligations; this delivery proves the assigned theorem from their
statements, as required by stage 3. It does not claim to close their transitive axioms.

## No longer needed

No public imports removed, no declarations removed and no modules withdrawn.
No new Sheaf dependency or intermediate theorem is needed. The original mathematical
steps (derived duality, perfect finite-dimensional point cohomology and cohomology of
the dual) are retained and implemented directly with the native Verdier-duality API;
no separate import of the generic field-complex or finite-coefficient pairing modules
is needed by this existential lisse-Weil-sheaf specialization. This does not withdraw
the broader blueprint statements or their dependency nodes.

## Where the brief, the DAG or earlier work was wrong

The main docstring's implementation note predates the now available native Verdier-duality
API. Although the derived cup product is still absent from this module's interface,
existence of a perfect Frobenius-invariant pairing follows from the existing equivariant
Verdier-exchange and smooth-duality isomorphisms. No canonical cup-product identity is
asserted by the assigned Lean signature, and the proof asserts none.

The blueprint node `thm-pod-degreewise-perfectness-over-a-field` has no current `lean`
attachment, and several of its generic proof dependencies have no current Lean attachment.
The assigned upstream theorem is its lisse Weil-sheaf existential specialization, rather
than its full generic perfect-complex/canonical-pairing statement. The proof instantiates
the existing derived-duality argument directly; it does not replace the unit's route or
change the statement or proof of that broader node. No DAG field changes are needed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
