Files written:

- dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-smooth-member.json — statement split, no Mathlib match.
- dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-singular-locus-dimension.json — statement-only supporting node, no Mathlib match.
- citations.json — verbatim statement excerpts for every cited node and step.

Attachments: none.

WANTED: none.

The item has no exact sorry-free declaration in the source. The matching Lean declaration in WeilConjectures.AlgebraicGeometry.Bertini is the separate finite-cover curve theorem and is sorry-backed, so it is not an attachment. I checked the imported statement against Stacks Tag 0FD6 and retained all hypotheses and the definition of “general”. The new supporting node isolates the universal-family singular-locus dimension estimate from the Bertini proof; it is strictly more technical than the item's conclusion and carries no proof steps at stage 1.

## Review by Q91

I read the item's source, literature/stacks-project/varieties.tex, Situation 0FD3 and Tag 0FD6, including the universal divisor, singular locus, fibre-smoothness, and base-change arguments. I also read the existing statements of def-pc-zero-scheme and def-pc-base-change cited in Step 1 and the base-change steps, and verified that their quoted sentences in citations.json are verbatim. Step 1 constructs the universal zero scheme and identifies its fibres using those definitions. Step 2 uses the new singular-locus node, whose statement gives exactly the dimension inequality and proper closed exceptional image used there. Step 3 takes the complement of that image and uses the fibre clause of the base-change definition to conclude smoothness of every parameter fibre. Step 4 checks that the same open is preserved by arbitrary field extension, matching the item's definition of “for general”. I ran the required Mathlib searches for the item and the new node with msearch.py; no Bertini or singular-locus theorem was found. I tested the edge case dim(V)=0 against the statement's nonempty-open conclusion and the generation/immersion hypotheses: such a system cannot satisfy the hypotheses on a nonempty smooth scheme, so no correction was needed. The server check_dag preflight passed.

What I could not finish: no Lean code was written or compiled, per the stage-1 instructions.

## Not duplicates

lem-zl-bertini-singular-locus-dimension vs lem-zl-bertini-smooth-member: the new node states only the dimension bound for the non-smooth locus of the universal divisor projection, while the item concludes smoothness of every parameter fibre on a nonempty open over all field extensions.
lem-zl-bertini-singular-locus-dimension vs lem-zl-bertini-finite-cover-curve: the new node is the universal-family dimension estimate for one linear system; the existing node is the iterated finite-cover curve construction with connected pullback and finite-field Frobenius descent.
