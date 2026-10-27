## What changed

Filled `AlgebraicGeometry.ProEtale.noetherian_finite_complex_heart_filtered_closure`
in `Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure`, preserving its signature,
universes, coefficient alternatives and all six conclusions. Added private proof imports
for the existing Noetherian heart and FP2 statements, the abstract FP2 Ind realization,
single-complex homology, sheaf Grothendieckness, and the Ext/universe-lift APIs.

The proof installs the finite closure and smallness instances supplied by the heart
statement. A proved private generic lemma computes homology as the cokernel of the map
to cycles. This identifies the finite-complex-heart property with constructibility;
the reverse inclusion uses the single complex in degree zero. Hom continuity gives
finite presentability after forgetting the additive structure. The normalized Yoneda
comparison, change of Ext universe and universe lift give the small Ext continuity
required by `fp2_ind_realization`. Its conclusions transfer along the equality of hulls.
The existing node's proof text records this implementation; its dependencies remain.

Validation: `lcompile.py` compiled the complete item in 14.6 seconds, with no
errors or warnings. The delivery tool additionally checks declarations and axioms.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.noetherian_finite_complex_heart_filtered_closure`
(node `lem-sfb-qcqs-finite-complex-heart-filtered-closure`).
No holes remain in the item module. No holes were added or split off.
The proof uses the already stated heart, FP2 continuity and FP2 Ind realization
theorems, whose existing holes are outside this delivery.

## No longer needed

No existing dependency node or module is pruned: all six planned dependencies remain
used, either as the three main statements or as the ambient-category infrastructure.
No existing import is removed. The separate image object in step 3 of the plan is
unnecessary: homology is directly the cokernel of the map from degree minus one to
cycles. This simplification needs no new statement.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The FP2 theorem states continuity of the actual
Yoneda functor in the ambient object universe, whereas the abstract Ind theorem uses
Ext in the indexing universe. The proof supplies the natural additive universe
comparison explicitly and reflects preservation through the fully faithful lift.
The zero complex and degree-zero single complex argument also apply to the empty
scheme and zero coefficient ring without extra hypotheses.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
