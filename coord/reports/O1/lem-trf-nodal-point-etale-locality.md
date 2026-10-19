# Worker report

Group N1; item `lem-trf-nodal-point-etale-locality`; stage 1 only.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-point-etale-locality.json`: item split into the two implications of Tag 0C57.
- `dag/nodes/sec-trace-formula/lem-trf-etale-completed-local-ring-iso.json`: new statement-only auxiliary node; no Mathlib declaration matches it.
- `citations.json`: verbatim quotations for every cited node in every item step.
- `searches.jsonl`: msearch records, including the revised searches for the auxiliary node.

## Attachments

None. I searched `WeilConjectures/` in both the slopmaster2 source and the upstream master for the item identifier and its nodal/etale notions; no finished declaration states the item exactly.

## Wanted

None. The Stacks sources used are present in `literature/stacks-project/`.

## Faults and corrections

The imported item was unsplit. Its statement is retained. The source Tag 0C57 is written for closed points after passage to an algebraic closure, whereas the item quantifies over arbitrary points. I made the missing reduction explicit in the auxiliary node: Tag 0478 gives the Jacobson property for schemes locally of finite type over a field, and Tag 039M gives the residue-degree and completed-local-ring description for an etale local map. If either point has residue field k, both points are closed, their residue fields agree, and their completed local rings are isomorphic. A nodal completed local ring has residue field k by the completion-residue-field node, so the two implications apply this auxiliary node and transport the presentation k[[u,v]]/(uv).

## Not duplicates

`lem-trf-etale-completed-local-ring-iso` vs `lem-trf-completed-stalk-isomorphism-etale`: the existing node assumes an isomorphism of completed stalks and concludes etaleness near a point; this new node assumes etaleness and a residue-field condition and concludes completed-local-ring invariance.

`lem-trf-etale-completed-local-ring-iso` vs `lem-trf-stalk-formally-unramified-maximal-residue-criterion`: the existing node characterizes formal unramifiedness by maximal ideals and residue extensions; it does not assert the scheme-level closed-point or completion conclusions here.

## Review by N1

I read the item node, the parent `lem-trf-nodal-family-etale-source-locality` proof, and `curves.tex` at Tag 0C57 together with the nodal completed-local-algebra definition. I also read `varieties.tex` at Tag 0478 and `etale.tex` at Tag 039M. The new auxiliary statement matches exactly the two source ingredients: local finite type over a field gives the Jacobson property, while an etale local map has completed target of rank the residue degree; when either residue field is k, the residue degree is one and the completion map is an isomorphism. The two item steps each use the verbatim statement of `lem-weil-pbc-local-completion-local-ring` to obtain the residue field k from the displayed nodal completion, then use the complete auxiliary statement to obtain closedness, residue-field identification, and completion identification before transporting the nodal presentation. I restored all nine definition dependencies appearing in the imported item statement, and kept the auxiliary node strictly smaller because it has no nodal-ring conclusion. I checked the identity etale map, a nodal point, a smooth point with completion k[[t]], and the vacuous empty-scheme case. No step exceeds 2000 characters, no SGA source is cited, and the Mathlib searches found only generic etale/residue-field APIs rather than this theorem.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-affine-maximal-points-closed-in-lft-scheme`: the existing node upgrades an affine-open closed point to an ambient closed point; the new node additionally uses the etale residue-degree theorem and concludes residue-field and completed-local-ring invariance.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-finite-type-nonclosed-closure-closed-points`: the existing node gives infinitely many closed specializations of a nonclosed point; the new node treats an etale point pair and proves closedness plus completion invariance from an algebraically closed residue field.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-integral-locally-algebraic-affine-opens-dimension`: the existing node concerns dimensions of affine opens in an integral scheme; the new node concerns residue fields and completed local rings for etale maps, with no integrality or dimension conclusion.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-lft-over-field-jacobson-space`: the existing node states density of closed points in closed subsets; the new node uses the Jacobson input to prove a specific etale point pair is closed and has isomorphic completions.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-point-tangent-closed-fibre-singleton`: the existing node proves a closed-fibre singleton under point-separation hypotheses; the new node has no point-separation hypothesis and instead proves etale residue and completion invariance.

`lem-trf-etale-completed-local-ring-iso` vs `lem-sc-positive-dimensional-locally-algebraic-closed-points`: the existing node concerns infinitely many closed points in positive-dimensional closed subsets; the new node concerns one etale point pair and completed local rings, with no positive-dimension assumption.

`lem-trf-etale-completed-local-ring-iso` vs `lem-coef-infinity-arrow-join-geometry`: the existing node is an infinity-categorical join-cone construction that merely cites the 0478 tag in its source metadata; it has no scheme point, residue-field, etale, or completed-local-ring statement.
