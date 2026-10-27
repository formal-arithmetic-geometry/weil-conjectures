## What changed

Pruned the unused auxiliary WeilConjectures.podCtfAdjunctions_exists from
Sheaf.Paper.PodCtfAdjunctions. Retained PodCtfAdjunctionData and all constructed
restriction functors and adjunctions, together with the already proved
AlgebraicGeometry.ProEtale.CondensedRing.podGeneralCtfAdjunctions. All retained
public signatures and definitions are verbatim.
All imports stay. Removed the obsolete compiled-signature fallback from the
compactification coherence invocation; the current theorem takes explicit k. The node's Lean attachment drops only the removed name;
proof_origin records the declaration-level pruning. Its mathematical statement,
dependencies and parent edges stay. The final proof step only drops its
obsolete signature-fallback explanation.

Change record: coord/changes/T2-prune-unused-pod-ctf-existence.md.

## Proved and sorry left

Initial holes: one, WeilConjectures.podCtfAdjunctions_exists (secondary attachment
of det-thm-sf-ctf-stability-adjunctions). Proved this session: zero. Pruned: that
one unused assertion. Added holes: zero. Remaining holes in the item: zero.
This is pruning, not a proof of the removed assertion and not a claim that the
retained general theorem's dependencies are sorry-free.

## No longer needed

Declaration WeilConjectures.podCtfAdjunctions_exists. No modules, imports or
DAG nodes are pruned: the item module and its mathematical node remain needed.

The full downstream list from tools/downstream.py is CoefficientGammaRepresentatives,
HomChainPairingNaturality, PodCtfPairingMaps, PodHomChainCounitFormula,
PodHomChainCtfDomains, PodHomChainUncurriedTransport, TensorHomCoefficientTransposes
and VerdierHomChainComposition (all under Sheaf.Paper). None mentions the removed
name. They quantify over supplied PodCtfAdjunctionData and use its explicit
ordinary, exceptional and tensor-Hom restriction constructions. The actual
three-clause general restriction theorem is already proved in this module.

Checked every DAG parent citing det-thm-sf-ctf-stability-adjunctions, including
unstated parents lem-pod-global-duality-map-identification,
lem-pod-smooth-pairing-point-transport, lem-pod-structure-hom-chain-realization
and sk-thm-sf-package. Their references are to the mathematical restrictions or
to the retained supplied data, not to this auxiliary arbitrary-datum existence
assertion. No unit realized field cites this node. No quarantined Lean source
uses the removed name or PodCtfAdjunctionData. Thus the node, its parents and
all unit routes are preserved; zero importers alone was not used as justification.

## Where the brief, the DAG or earlier work was wrong

The remaining sorry is not part of the implemented general restriction proof.
An earlier review already called podCtfAdjunctions_exists an unused sorried
four-stage theorem. Its stronger extra assertion supplies a closed presentation
for arbitrary operation data, while the consumers intentionally take such a
presentation as a parameter. Keeping that unused assertion would create proof
work that neither the implemented parent proofs nor the node's three-clause
restriction proof uses.

Searches: msearch leanfinder found Mathlib's fullMonoidalClosedSubcategory;
loogle found restrictFullyFaithful and its Hom formula. Local source and DAG
searches identified the existing general proof and absence of callers. No
Mathlib search is claimed as a proof of the removed existence assertion.

There are no new statements, no weaker replacement, no new choice of data,
no source-library edits and no forced adaptations.

The first compile passed in 11.3 seconds but flagged the old compactification
coherence signature fallback as unused and unreachable. The current published
signature has explicit k, so the final source invokes that signature directly.
The last node proof step now records this invocation.

Final lcompile passed without errors or warnings in 29.0 seconds. The static
import/declaration pruning check also passed for all current downstream sources.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
