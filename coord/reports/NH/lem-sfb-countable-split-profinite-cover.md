# Stage-1 report: lem-sfb-countable-split-profinite-cover

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-countable-split-profinite-cover.json`: statement split, no new nodes, Mathlib verdict no match.
- `citations.json`: citation quote for the universe dependency.

## Attachments

None. No finished declaration in the upstream Lean source states this item.

## WANTED

WANTED: an external reference for the countably split Cantor-cover construction (the blueprint itself marks this pure-topology input as WANTED); the proof is supplied directly as an agent proof.

## Not duplicates

No duplicate node was found in the DAG or in either blueprint snapshot; the existing profinite and Cantor nodes concern general profinite limits or arbitrary Cantor surjections and do not state prescribed two-point fibres with clopen off-diagonal relation points and tail density.

## Statement and source review

The imported statement is retained verbatim apart from completing the malformed typography around “metrizable”. It is a pure-topology auxiliary in Paragraph (3) of the main-20261015 open-direct-image proof. The source explicitly says the blueprint does not assert the input and requests an external reference, so I used `proof_origin.by = agent` and wrote the construction out.

## Review by NH

I read the item node, its source paragraph, the unit and chapter records, the existing profinite/Cantor DAG candidates, and the Mathlib search results. Step 1 fixes Cantor space, an order-preserving ternary embedding, a distinct countable dense sequence whose every basic cylinder is hit infinitely often, and summable jump sizes; the universe convention is the only DAG statement dependency and is quoted verbatim in `citations.json`. Step 2 defines the lexicographic step functions and proves uniform convergence, continuity off the selected points, and the two distinct one-sided limits at each selected point. Step 3 takes the graph closure in a compact metric product, proves surjectivity of the projection, and computes singleton versus double fibres by the side limits. Step 4 checks total disconnectedness by projecting connected subsets to the totally disconnected Cantor base and using the finite fibres. Step 5 checks the relation-space condition: the tail amplitudes force fibres over nearby indexed points toward the centre height, so a clopen base cylinder and two small vertical intervals isolate each ordered off-diagonal pair; Hausdorffness makes the singleton closed. Step 6 uses density of the graph and compact-to-Hausdorff closedness of the projection to find an open base neighbourhood whose entire fibres lie in a given open subset, then uses the tail-dense enumeration to obtain arbitrarily high double fibres there. I checked endpoint exclusion, nonempty spaces, distinctness of the two limits, and the cases of singleton fibres. The Mathlib searches were rerun with the target id and recorded in the node; they found only generic Cantor/profinite/compactness declarations, so the target remains an agent-proved pure-topology statement.

## What I could not finish

Nothing remains beyond the requested external-reference WANTED line; the agent proof supplies the missing construction.
