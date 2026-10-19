# Worker report

Files written:

- \`dag/nodes/sec-trace-formula/lem-trf-alteration-relative-curve-preparation.json\`: split item with three proof steps and no remaining sorry or Lean attachment.
- \`dag/nodes/sec-trace-formula/lem-trf-relative-curve-factorization.json\`: statement-only unsplit node; Mathlib searches found no match.
- \`dag/nodes/sec-trace-formula/lem-trf-generic-smooth-boundary-preparation.json\`: statement-only unsplit node; Mathlib searches found no match.
- \`citations.json\`: verbatim statement excerpts for every citation used by every item step.

Attachments: none. No sorry-free declaration with the exact item statement exists in the searched Lean source.

WANTED: none.

## Not duplicates

- \`lem-trf-relative-curve-factorization\` vs \`lem-fin-generic-curve-model\`: the existing node treats projective morphisms whose geometric fibres already have dimension at most one and constructs a finite normalization comparison; the new node factors an arbitrary proper integral family of generic-fibre dimension \(d\geq1\) through a base of dimension \(d-1\) with relative function-field transcendence degree one.
- \`lem-trf-generic-smooth-boundary-preparation\` vs \`lem-pur-finite-inseparable-geometric-reduction\`: the existing node only makes a reduced finite-type scheme geometrically reduced after a purely inseparable field extension; the new node simultaneously spreads the extension over a projective alteration of \(Y\), normalizes the relative curve, and gives a smooth irreducible generic fibre with a finite étale reduced boundary.
- \`lem-trf-generic-smooth-boundary-preparation\` vs \`lem-sbc-radicial-generic-reduced-preparation\`: the existing node is an affine radicial preparation preserving geometric irreducibility and reducedness without flatness; the new node concerns a proper relative curve, projective alteration, normalization, smoothness, and the reduced inverse image of a nowhere-dense boundary.

## Review by Q82

I read the imported item and its source citation, the chapter and unit records, the current blueprint ancestry, and the complete proof of Exposé X, Theorem 3.5, Steps 2 and 5 in the supplied Illusie–Laszlo–Orgogozo PDF. I also searched the project DAG and the Lean source for the item tag and for relative-curve, transcendence-basis, schematic-image, smooth-generic-fibre, and purely-inseparable preparation declarations. No exact Lean declaration or existing node gave the item.

Step 1 cites the new factorization node, whose statement supplies the projective integral \(Y_0\), its generic-fibre dimension \(d-1\), the proper dominant generically finite alteration \(a\), the map \(g\), the factorization through \(Y_0\), and relative transcendence degree one. Step 2 cites both the factorization statement and the new preparation statement; the latter explicitly supplies the finite purely inseparable projective alteration, the schematic-closure replacement, the resulting maps, the smooth irreducible generic curve, and the finite étale reduced inverse boundary. Step 3 cites the same two statements and the existing dimension–transcendence-degree node; it checks that finite purely inseparable generic-field extensions are algebraic, so the generic-fibre dimension remains \(d-1\), and then renames the prepared objects. The only elementary part is the renaming/composition of the displayed compatible maps and the observation that algebraic extensions do not change transcendence degree.

I checked the hypotheses on the small cases \(d=1\), \(Z=\varnothing\), and \(S=\operatorname{Spec}(k)\): the base \(Y\) has zero-dimensional generic fibre when \(d=1\), and the boundary conclusion permits the empty finite étale scheme. The trait case uses only the generic fibre and the excellence/projectivity hypotheses stated in the nodes. Each new node is deliberately statement-only because its alteration and generic-smoothness existence theorem is the non-elementary input from the cited source. All Mathlib searches were run with Q82's search tool for the item and both new nodes; the logs record the exact queries and the unavailable Loogle identifier queries as unavailable.

