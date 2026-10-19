## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-fibre-component-closure-dimension.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-associated-equidimensional.json` — statement-only node, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fibre-component-relative-associated.json` — statement-only node, no Mathlib match.
- `citations.json` — verbatim statement quotations for every cited step.

## Attachments

None. I searched the slopmaster2 WeilConjectures source by item id, keywords, and blueprint tags; no sorry-free declaration states this item exactly.

## WANTED

None.

## Not duplicates

- `lem-trf-flat-associated-equidimensional` vs `lem-trf-flat-dense-generic-fibre-pure-dimension`: the new node is the general relative-assassin equidimensionality theorem for the closure of one relative associated point; the existing node assumes an integral base and dense pure-dimensional generic fibre and concludes purity of every fibre and geometric fibre.
- `lem-trf-flat-associated-equidimensional` vs `lem-trf-flat-family-generic-dimension-bound`: the new node gives equality of all fibre component dimensions from a relative associated point; the existing node gives only an upper bound from a generic-fibre support dimension hypothesis.
- `lem-trf-fibre-component-relative-associated` vs `def-sc-associated-points`: the new node identifies generic points of scheme-theoretic fibres with relative associated points; the existing definition only defines ordinary associated points of a scheme's structure sheaf.

## What was wrong or changed

The imported item was unsplit, with the proof and dependency lists empty. Its source is the specialization of Stacks Tag 0GSJ to the structure sheaf, with the relative-assassin definition and fibrewise generic-point fact as inputs. I kept the statement and all hypotheses unchanged, including the absence of integrality or purity assumptions on the base and other fibre components. The split isolates the genuinely reusable 0GSJ theorem and the fibrewise associated-point fact instead of restating the item's conclusion.

## What I could not finish

No Lean declaration was written or compiled, as required for stage 1.

## Review by Q31

I read the item node, the `sec-trace-formula` chapter, the `sk-i-curve-zero` unit, and the source passages in `literature/stacks-project/more-morphisms.tex` (Tags 0GSI, 0GSJ and 0GSK), `divisors.tex` (Tags 02OZ and 02OJ), and `morphisms.tex` (Tags 01T6 and 02NJ). I also inspected the slopmaster2 source and found no declaration carrying the item blueprint id or an exact equivalent. The two new nodes were searched against the whole DAG and blueprint before writing; the search found no duplicate or blueprint node with the same statement.

Step 1 uses the statement of `lem-trf-fibre-component-relative-associated`: it explicitly says that a generic point of a fibre irreducible component is an associated point of the fibre structure sheaf and hence lies in the relative assassin. The fibre is locally Noetherian because the morphism is locally of finite type over a field (Tag 01T6), so the generic-point associated-point assertion applies. Step 2 uses `lem-trf-flat-associated-equidimensional`: its hypotheses match the item after taking `\\mathcal F=\\mathcal O_X`; global flatness of `f` supplies flatness at every generic point of every fibre of the closure. Step 3 uses the same node for the constant relative dimension and the cited fibre, irreducible-component, and topological-dimension definitions to identify the fibre of the closure over `t` with the chosen component `B`. The only elementary move is this underlying-space identification and the equality `d=dim B`; no hidden existence or comparison lemma is folded into it.

I tested the statement on a constant family `Spec(k[x])\\to Spec(k)`, on a flat family with reducible special fibre `k[t,x,y]/(xy-t)`, and on the zero-dimensional fibre case; the asserted equality gives the expected dimensions. I also checked that the argument never assumes the reduced closure is flat, that the base is integral, or that unrelated components of `X_t` have the same dimension. Mathlib searches for each node and the item used LeanFinder, Loogle, and Mathlib grep in two phrasings where applicable; all returned only general flatness, going-down, generic-point, or smooth-dimension declarations and no match. The recorded queries and results are in the node JSON files.
- `lem-trf-fibre-component-relative-associated` vs `pqf-lem-locnoeth-lft`: the existing node only states local Noetherianity of a locally finite type morphism over a locally Noetherian base; it does not identify fibre generic points as associated points.
- `lem-trf-fibre-component-relative-associated` vs `pqf-def-locnoeth`: the existing node defines local Noetherianity, while the new node gives the associated-point conclusion for a scheme-theoretic fibre.
- `lem-trf-fibre-component-relative-associated` vs `lem-weil-pbc-finite-algebra-noetherian`: the existing node concerns Noetherianity of finite algebras; it has no relative-assassin or fibre-component statement.
- `lem-trf-fibre-component-relative-associated` vs `lem-weil-pbc-finite-type-over-noetherian`: the existing node concerns finite type over a Noetherian base, not associated points of fibre components.
- `lem-trf-fibre-component-relative-associated` vs `lem-weil-pbc-graded-finiteness-cohomology`: the existing node uses finite type over a Noetherian base for graded cohomology finiteness, with no associated-point conclusion.
- `lem-trf-fibre-component-relative-associated` vs `lem-sbc-composite-fibre-local-models`: the existing node constructs local models for composite fibres; it does not state the relative-assassin fact.
- `lem-trf-fibre-component-relative-associated` vs `lem-pur-affine-line-support-geometry`: the existing node concerns support geometry of an affine-line family, not generic points and associated points of arbitrary fibres.
- `lem-trf-fibre-component-relative-associated` vs `lem-trf-proper-base-change-coherent-conservative`: the existing node is a conservativity statement for coherent pushforward, not a fibre associated-point lemma.
- `lem-trf-fibre-component-relative-associated` vs `def-sc-no-embedded-points`: the existing node defines absence of embedded points via associated points of a locally Noetherian scheme; it does not assert the relative fibre statement.
- `lem-trf-fibre-component-relative-associated` vs `lem-sc-regular-meromorphic-section-exists`: the existing node uses associated points in a regular-section argument but does not identify fibre generic points as relative associated points.
- `lem-trf-fibre-component-relative-associated` vs `lem-sc-invertible-module-generic-stalk`: the existing node concerns invertible-module generic stalks and does not state the fibre-associated-point conclusion.
- `lem-trf-flat-associated-equidimensional` vs `lem-trf-flat-fibre-component-closure-dimension`: the existing item is the specialized conclusion for the structure sheaf and one fibre component; the new node is the general Tag 0GSJ theorem for an arbitrary finite-type quasi-coherent module and relative associated point.
- `lem-trf-flat-associated-equidimensional` vs `lem-trf-flatification-horizontal-curve-pair`: the existing node uses Tag 0GSJ only to record pure dimensions of two specific flatified curve components; it does not state the general relative-assassin theorem.
