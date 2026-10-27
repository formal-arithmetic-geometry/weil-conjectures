## What changed

Proved AlgebraicGeometry.coherent_property_devissage in
Sheaf.AlgebraicGeometry.CoherentPropertyDevissage from the existing filtration,
irreducible-support, coherence and closed-pushforward APIs. The Lean proof uses
well-founded induction on closed supports followed by Fin.induction on a finite
coherent filtration. All helpers are proved local facts; no declaration is split off.
The source statement is repaired to require a generic point and the canonical
quotient scalar action; see
coord/changes/coherent-property-devissage-residue-action.md.

Updated lem-pc-coherent-property-devissage's proof, proof_deps, proof_origin and
Lean statement to match. Its natural-language statement now explicitly says that
the residue-field action is induced by the stalk-ring action. Retained the unit's
route through coherence, integral filtration and irreducible-support devissage.
Added private proof imports for coherent kernels/cokernels, coherent submodules,
finite pushforward, closed-pushforward stalks and affine quasi-coherent pushforward.
No public import is changed. The declaration's docstring now describes the actual proof.

## Proved and sorry left

Closed the one existing hole in AlgebraicGeometry.coherent_property_devissage
(lem-pc-coherent-property-devissage), after the documented source-faithful interface
repair. Proved 1 of 1 item holes; zero holes remain in the item; zero holes added;
zero split off. This is a proof from existing named declarations, including the
pre-existing sorry in coherent_property_irreducible, not an axiom-free proof of that
dependency. No original signature is retained under a new name with a moved hole.

The item compiled through lcompile.py. The direct consumer is checked unchanged
against the sandbox's compiled repaired criterion; its existing sorry is untouched.
The delivery tool also probes all declarations' axioms and holes.

## No longer needed

Removed the private import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
and the dependency lem-weil-pbc-integral-scheme-ideal-generic-stalk, including both
obsolete top-level tool_uses entries. The induction directly proves P for all ideal
pushforwards with image contained in a closed bound, so no calculation that a
filtration quotient has full integral support is needed. Closed-pushforward stalks
supply only the containment in the image required by the irreducible-support lemma.
This prunes the dependency from this node's proof; its upstream module remains
available and is still needed by other proofs. The integral-filtration and
irreducible-support dependencies remain necessary. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old Lean attachment did not require ξ to be generic and allowed an unrelated
existential residue-field Module structure. The source uses only generic points
and the action induced from the original stalk-ring action. Corrected both in the
same delivery, preserving the conclusion and matching the already-correct
irreducible-support lemma. The quotient action is essential: the bare existence
of an unrelated one-dimensional action is not the scalar dimension in the source.
For example, over Spec Q(t), take P to mean even canonical vector-space dimension.
It satisfies zero and two out of three, and the additive group of Q(t)^2 is
isomorphic to that of Q(t) (both have countably infinite dimension over Q).
Transporting the one-dimensional Q(t)-action along this additive isomorphism makes
the canonical rank-two module a witness for the old unrelated-action hypothesis,
but the canonical rank-one module does not satisfy P. The repaired action equation
excludes precisely this defect; the new theorem states the source criterion.
On an empty scheme the integral hypothesis is vacuous but hP_zero covers every
module; zero ideals and length-zero filtrations are included by the proof.

The one DAG citer, lem-trf-curve-euler-tensor-generic-rank, still holds: its
witnesses are structure modules at generic points, with the canonical quotient
action. Its Lean proof remains sorry and contains no old application. All 11
transitive consumers are listed in the change record; no adaptation is needed.
The source's minimal-counterexample argument is implemented as equivalent
well-founded induction, and the unnecessary generic-support calculation is omitted.

Searches used the required leanfinder, loogle and grep commands and local rg;
no Mathlib theorem proved this devissage criterion. The proved 01YM criterion
in the source library has different integral witness hypotheses and is not a
shortcut to the existing 01YH route. No agents were started and no independent
second-reading section is claimed, as required for dispatcher workers.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
