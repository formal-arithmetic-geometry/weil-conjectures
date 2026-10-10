Files written:

- `dag/nodes/sec-smooth-purity/def-amb-finite-locally-free-module.json`: definition, no new child nodes, Mathlib search verdict no exact match.
- `citations.json`: empty because the item is a definition and has no proof steps.

Attachments: none. No WANTED items.

The imported item was not already stated by a project declaration carrying the blueprint tag. The related Mathlib declaration `SheafOfModules.IsFiniteLocallyFreeOfRank` uses local-generators data on an arbitrary Grothendieck site; it does not state this scheme-specific Zariski-cover definition, so it is not an attachment or Mathlib leaf. The existing dependency `pqf-def-coherent` is retained for the quasi-coherent-module convention. No statement error or source error was found.

## Review by M1

I read the imported node, its recorded master-blueprint source path and the unit record `sk-prop-an`. The node says exactly that an \(\mathcal O_S\)-module on a scheme is locally free of fixed rank \(d\) when it is isomorphic to \(\mathcal O^{\oplus d}\) on a Zariski open cover, and records quasi-coherence as the convention used later. I checked the existing `pqf-def-coherent` dependency is the node that names quasi-coherent modules. I searched the project Lean sources for the blueprint tag and the locally-free terminology; no sorry-free project declaration states this item. I also ran both phrasings of LeanFinder, Loogle, grep, and LeanSearch required by the brief. LeanFinder returned only abstract local-generators and finite-type predicates; Loogle and grep returned no exact declaration, and LeanSearch was unavailable on both attempts. The small cases \(d=0\) (zero module on each cover), \(d=1\) (invertible/local rank-one case), and the empty scheme satisfy the stated cover definition. Since this is a definition node, there are no proof steps or node citations to quote; the citation list is therefore empty. I preserved all imported blueprint, audit, and import fields and changed only the split-owned status, blueprint `same_as`, search record, and split report.

What could not be finished: no project or Mathlib declaration exactly attaches to this scheme-specific definition; the required LeanSearch service was unavailable, recorded as such.

## Second reading by M1

- Item statement: checked against the recorded blueprint node `def-amb-finite-locally-free-module` (order 1967), including the scheme, module, Zariski-cover, fixed-rank, and quasi-coherence clauses; verdict: agrees hypothesis by hypothesis.
- Proof steps: none; this is a definition node with empty `proof` and `proof_deps`, so there are no dependencies or citations to audit.
- New nodes: none; no child node is needed for a definition, and the recorded Mathlib searches found only abstract local-generators predicates rather than this scheme-specific definition.
- Edge cases: checked rank `d=0` (zero module), rank `d=1` (invertible-module case), and the empty scheme; verdict: all satisfy the cover definition.
- Form and provenance: checked self-contained TeX, `pqf-def-coherent` as the quasi-coherence statement dependency, blueprint fields, and the recorded LeanFinder/Loogle/grep/LeanSearch logs; verdict: compliant.

No changes were needed after the second reading. The sandbox contents remain unchanged because the node, searches, and worker review already satisfy the delivery requirements.
