## What changed

Proved `WeilConjectures.PurityFiniteSetting.sectionInvariant_invertible` by canonical
comparison with the existing finite comparison-coordinate section invariant. The
compactification of g is Noetherian over the finite-type base B, so its open subscheme
V is Noetherian and g is quasi-compact. The coefficient unit comparison and the
invertible unit of the bounded-below comparison adjunction identify P.dualizing with
finiteComparedDualizing. Applying the actual derived pullback identifies the section
objects. Transport constructible finite-Tor membership and both tensor inverse
identities from comparedSectionInvariant_invertible along this isomorphism.

Added proof-only imports of Sheaf.Paper.PuritySectionInvariantCompared and
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison. Existing
public definitions, theorem signatures, public imports and docstrings are unchanged.
The proof compiled on the server in 12.7 seconds; the sole line-length warning was
corrected before the delivery checks. Import-direction checking confirms no cycle.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.sectionInvariant_invertible`
(blueprint def-pur-section-invariant). No sorry remains in the item, and no hole,
module or declaration was added. The proof uses the existing theorem
`WeilConjectures.PurityFiniteSetting.comparedSectionInvariant_invertible`; its
pre-existing hole is neither changed nor duplicated by this delivery. This proves
the assigned theorem from existing declared dependencies, not its full axiom closure.

## No longer needed

No original imports removed; no node or module is claimed globally pruned. The
finite-clopen and pure-dimensional argument is reused through the existing
comparison-coordinate invertibility theorem; those steps and their dependencies
remain needed there. No direct imports of the clopen decomposition, clopen
exceptional restriction, smooth dimension loci, pullback Tor-amplitude, or pullback
tensor comparison modules are needed in this legacy interface adapter.

The temporary proof import Derived.UpperShriekFiniteness was removed: its comparison
is constructed directly by applying the published comparison adjunction unit and the
etale exceptional functor. The two remaining added imports are both used.

## Where the brief, the DAG or earlier work was wrong

The node def-pur-section-invariant now attaches to PuritySectionInvariantIntrinsic,
not to this dispatched legacy fixed-scalar module. Its newer attachment and proof
route are left intact, since this delivery changes only the legacy adapter proof.
The comparison-coordinate theorem requires quasi-compactness and separatedness;
the proof derives them from the original compactification and finite-type base
assumptions, without adding hypotheses. Its argument accommodates the empty scheme
and varying smooth relative dimension through that existing theorem.

The initial compiler attempts received no service response. A later response showed
that the published build lacked Derived.UpperShriekFiniteness.olean. Removing that
proof dependency in favor of the underlying comparison adjunction resolved the
missing-artifact failure; no shared file or launcher tool was changed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
