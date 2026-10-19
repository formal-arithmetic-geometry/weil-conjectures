# Stage-1 report: def-cbc-enhanced-cartesian-fibration

## Files written

- `dag/nodes/sec-smooth-purity/def-cbc-enhanced-cartesian-fibration.json`: existing definition updated to `status: split`; zero new nodes and zero proof steps.
- `citations.json`: empty list, because a definition-only split has no proof steps.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its descriptive names, and the blueprint tag found no project declaration. No sorry-free declaration states this definition.

## WANTED

- Archived Kerodon, Proposition 7.4.4.1 (Tag 05RX), Corollary 7.4.4.2 (Tag 02TK), Definition 5.6.5.1 (Tag 028V), and Subsection 5.6.4 (Tag 0279), for the cocartesian-section and transport conventions.
- Lurie, *Higher Topos Theory*, Section 3.2.2, especially Notation 3.2.2.3 and Definitions 3.2.2.6–3.2.2.7, for mapping simplices and strict presentations.

## What was checked

The item source is the imported node's Kerodon/HTT citation. I read [def-cbc-enhanced-diagrams-cones], [def-coef-infinity-fibrations], [lem-coef-coherent-nerve-comparison], [lem-cbc-grothendieck-presheaf-coherent-straightening], and [lem-cbc-grothendieck-hypersheaf-sections]. The existing cited nodes define the simplicial-set, quasicategory, universe, internal-functor, core, and cartesian/cocartesian-fibration notions used by the item; this item then defines the remaining section and strict-presentation data inline.

Because the node is a definition, there are no proof steps and hence no cited statements to quote in `citations.json`. I checked each clause directly: a section over `p:X→S` is a map `S×Δ^r→X` over `S` with precomposition operators; the cocartesian section subobject imposes the edge condition while retaining arbitrary higher transformations; the opposite convention reverses vertices and faces; `Cat_∞` is the stated homotopy-coherent nerve in a containing universe; the strict functor laws are explicit; the marked Grothendieck construction has the stated simplex operators, marked degenerate edges, fibres, and cocartesian variance; and a strict presentation is exactly a map over `N(C)` preserving marked edges and fibrewise equivalences. I tested the empty category, a one-object category, a discrete two-object category, and a single-arrow category against these formulas. No hypothesis is added or omitted, and no construction is silently identified with an inner fibration.

I searched the whole DAG and both blueprint snapshots for the item concepts and found no duplicate or alternate blueprint statement. I ran fresh LeanFinder, Loogle, Mathlib grep, and LeanSearch queries; they returned only ordinary nerve, strict-Segal, inner-fibration, or simplicial-enrichment declarations, so the item is not a Mathlib leaf. The existing `blueprint.from` ancestor and opening-choice place are retained, with `same_as: []`. No source or statement correction was needed.

## Review by NH

I reviewed the final JSON against the source and all statement dependencies. Since every object required by the definition is either imported from a cited definition node or introduced by an explicit formula here, adding a theorem node would duplicate a clause of the definition. The compact-support route uses this node only as a vocabulary/interface definition; the later cocartesian-section lemma carries the actual comparison theorem. I verified that no step, proof dependency, or hidden theorem claim remains, and that the Mathlib search records match the four searches run on 2026-10-17. The split is therefore a zero-new-node definition split.

## What was wrong or incomplete

The imported node had no proof metadata and was unsplit, but its statement itself was complete. The source links are online references marked WANTED because the archived copies are not present; this affects citation availability only, not the explicit definition. No mathematical statement error was found.

## What could not be finished

Nothing within stage 1. The external Kerodon and HTT texts remain WANTED for later source verification.

## Second reading by NH

- Item statement: checked every clause against the imported Kerodon/HTT and six-functor-notes source places, and against the three cited definition nodes; the section, opposite, nerve, strict-functor, marked Grothendieck, fibre, marking, and strict-presentation clauses are self-contained and retain the stated edge cases.
- Proof steps: none; this is a definition-only split, so there are no dependency statements or citations to audit.
- New nodes: none; no auxiliary theorem or duplicate definition was introduced.
- Small cases: checked empty and one-object categories, a discrete two-object category, a single-arrow category, and the empty/point section bases; the formulas are well-typed and behave as stated.
- Searches: checked the whole DAG, both blueprint snapshots, source trees, and Mathlib; no duplicate node or exact Mathlib declaration was found, and the recorded LeanFinder, Loogle, grep, and LeanSearch results are genuine no-match results.

Changes made during second reading: none. The existing repaired definition and report already satisfy the stage-1 contract; delivery preflight and DAG review pass.
