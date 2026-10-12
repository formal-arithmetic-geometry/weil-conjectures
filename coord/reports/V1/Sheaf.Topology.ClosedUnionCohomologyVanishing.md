## What changed

Completed `TopCat.cohomology_vanishing_of_closed_union` without changing its
signature or docstring. Added proof-only imports of
`Sheaf.Topology.NoetherianOpenClosedCohomologySequence` and
`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`.
A proved private helper transports vanishing through the existing
closed-embedding cohomology comparison and Ext change of universe.

The proof constructs the open complement of Z in T = Z union W, applies the
existing open-closed sequence, and maps its closed complement into Z and the
closure of its open into W. The universal hypotheses kill the outer
cohomology groups; `Abelian.Ext.covariant_sequence_exact₂` kills the middle.
Updated the existing node's proof steps to describe these concrete maps and
the universe conversions. The proof dependencies and unit route are unchanged.

## Proved and sorry left

Proved `TopCat.cohomology_vanishing_of_closed_union` (1 of 1 original sorries)
and private `TopCat.zero_cohomology_of_closed_embedding`.
No sorry remains in the item, and this delivery adds no sorry.
The imported existing declarations
`TopCat.noetherian_open_closed_cohomology_sequence`
(node `lem-sc-noetherian-open-closed-cohomology-sequence`) and
`TopCat.cohomology_closed_immersion_pushforward`
(node `lem-sc-cohomology-closed-immersion-pushforward`) remain proof dependencies.

## No longer needed

No original library import, node, or module is pruned: all three original
proof dependencies are used. Removed the earlier sandbox-only module
`Sheaf.Topology.ClosedUnionCohomologyReduction` and node
`new-node-closed-union-cohomology-reduction`; neither is part of this delivery.
No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt restated the entire conclusion as an isomorphism
to a zero group. It was not a reduction and has been discarded.
The node's planned site-equivalence transport is unnecessary: closed embeddings
from the relative closed subspaces directly into Z and W let the universal
hypotheses apply after pushforward. This follows the same open-closed argument
in Stacks 02UZ, using 02UT and 02UV. The original statement is unchanged.

Checked the geometric construction for empty, equal and nested Z and W:
closed subtype embeddings and closure containment still hold. The Ext exactness
lemma applies to every natural degree q, including zero, so no predecessor-degree
or intersection-vanishing hypothesis is introduced.

Local compilation passes without warnings. Searches through Lean Finder,
Loogle, Mathlib grep and the source library did not give a direct closed-union
vanishing theorem; the existing sequence and Mathlib Ext exactness suffice.

## Second reading by V1

1. Compared the delivered module and node with the repository versions. The theorem signature and existing declarations are unchanged; the proof-only imports and proof body are the only Lean changes, and the node proof text/dependencies match the implemented route. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. An axiom probe reports only the permitted axioms plus `sorryAx` inherited from the documented imported declarations. There are no local `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. Verdict: pass.

3. The private helper is a genuine transport lemma for closed-embedding cohomology and is not a restatement of the target. Searches of the repository and Mathlib found no existing theorem duplicating the target or helper. No split-off statements or new nodes were added. Verdict: pass.

4. The proof follows the unit route through the noetherian open-closed sequence and closed-immersion comparison, then uses Mathlib Ext exactness. Both added imports are proof-only and used; no old proof dependency or unit node is pruned. Verdict: pass.

5. The DAG node's proof steps, dependencies, origin, Lean declaration, and unit are consistent with the proof. Verdict: pass.

Changed: added this second-reading report section only; no source or DAG repairs were necessary.
