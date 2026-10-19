Files written:

- `dag/nodes/sec-trace-formula/def-trf-log-regular-pair.json`: definition; no Mathlib match; no new nodes.
- `citations.json`: empty, because a definition has no proof steps.

Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the exact project definition; the only keyword hit was unrelated Riemann–Roch text. Whole-DAG and blueprint searches found no duplicate definition or equivalent blueprint node. The four existing statement dependencies are the notions actually used in the definition.

WANTED: none.

The imported statement is mathematically coherent and was kept unchanged. It explicitly distinguishes the divisorial log structure from its fine-saturated charts, the strict-local pushout chart condition, the triviality locus, and the regular-stratum dimension equation. No proof step is present because this is a definition; consequently there are no proof dependencies or citation quotes. Mathlib searches returned only general smoothness, regularity, and Krull-dimension declarations, with no logarithmic-geometry definition.

## Not duplicates

`def-trf-log-regular-pair` vs `lem-trf-snc-divisorial-log-chart`: the latter proves log regularity for a smooth strict normal-crossings pair and uses this definition; it does not define the general divisorial notion.

`def-trf-log-regular-pair` vs `lem-trf-nodal-log-regularity`: the latter proves log regularity of a marked nodal family over a log regular base; it is a theorem about a special construction, not the definition.

## Review by Q121

I read the complete item and its chapter and unit records, then checked the source place in Illusie–Laszlo–Orgogozo, Exposé VI, §§1.1–1.4 (printed pages 69–70). I read each cited dependency: `pqf-def-locnoeth` supplies locally Noetherian schemes, `def-pc-scheme` supplies closed subsets and dense open complements, `def-weil-pbc-etale-site` supplies the small étale site, and `def-weil-regular-scheme` supplies regularity. The definition uses exactly those notions and introduces the remaining monoid, chart, strict-local, characteristic-monoid, ideal, dimension, and rank terminology inline. Because the node is a definition, it has no proof steps to cite and `citations.json` is empty. I checked edge cases in the statement: (Z=\varnothing) gives (M=\mathcal O_V^\times), the characteristic monoid has rank zero, and the triviality locus is all of (V); at points of (Z), the prescribed nonunit ideal and quotient condition apply. I also searched the project Lean source for the item tag and log-regular terminology, searched the whole DAG and blueprint for duplicates, and ran the required LeanFinder, Loogle, grep, and LeanSearch queries through `msearch.py`; all relevant hits were generic smoothness/regularity facts, so there is no Mathlib match. No correction was needed.

What I could not finish: nothing; this definition-only split is complete and ready for delivery.
