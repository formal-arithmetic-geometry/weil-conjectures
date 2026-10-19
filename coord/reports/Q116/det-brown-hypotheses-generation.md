Files written:
- `dag/nodes/sec-six-functors-basics/det-brown-hypotheses-generation.json`: existing item split into seven proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for all 17 step citations.

Attachments:
- None. No finished sorry-free declaration in `WeilConjectures/` states this item exactly.

WANTED:
- None.

The item statement and its seven-step proof were compared with the current main-20261015 Brown generation blueprint and the current DAG statements. The finite coefficient case uses the existing finite compactness theorem. The rational case first checks qcqs and the exact finite-subextension-valued coefficient ring, then uses the Qbar two-colimit identification and the ambient filtered-colimit category before invoking rational compactness. The integral case checks the O_E coefficient object, ordinary derived module ambient category, all field and finite-extension hypotheses, and the ctf=Dbc identification. The generation argument defines the right orthogonal class, proves shift and cone closure (including reverse rotation for the middle object), proves arbitrary coproduct closure including the empty family, and applies localizing-closure minimality.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to distinguish. Existing cited nodes were searched in the whole DAG by their ids and key phrases before retaining them.

## Review by Q116

I read the item node, `dag/units/sk-lem-brown-hypotheses.json`, the chapter record, and the current blueprint node and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-brown-hypotheses/sk-lem-brown-hypotheses-generation.md` and its `.proof.md`. I also read every cited node named by each step. Step 1 uses only `det-ctf-finite-compact-proetale`, whose statement gives compactness for every finite-coefficient constructible finite-Tor object. Step 2 uses the finite-type, separated-affine-intersection and qcqs-cover statements for the geometric hypotheses, the Qbar two-colimit clause identifying the rational constructible classes, `det-def-localizing-closure-existence` for the fixed ambient closure and coproducts, `det-ambient-ind-derived-sums` for membership in the filtered-colimit ambient subcategory, and `sk-thm-constructible-compactness` for the displayed Hom/direct-sum isomorphism. Step 3 uses the integral ctf=Dbc statement, the integral compactness theorem (including its O_E ring, characteristic, finite-extension, separated finite-type hypotheses and ordinary derived ambient category), and the generic closure theorem. Steps 4 and 7 use the closure theorem for the fixed ring; step 5 uses the stated triangulated shift/TR axioms and the exact Hom-out-of-triangle statement; step 6 uses the same shift equivalence and coproduct universal property. The `citations.json` quotes are copied verbatim from the cited statements and checked for every step/node pair.

I checked edge cases in the proof route: empty scheme and point scheme, zero object, shifts -1, 0 and 1, empty coproduct, E = Q_l (giving Z_l), and finite coefficient Z/l^2. The item now explicitly has the global finite-field datum k = Fbar_q required by the current rational compactness theorem; the arbitrary-field version is false in infinite cohomological dimension. The current finite-subextension-valued Qbar coefficient convention is used consistently, with no comparison to the conflicting unrestricted convention. No SGA source is cited. The existing item has no new node to search or split, and its proof dependency list is exactly the union of its step uses.

The initial dry run refused an unchanged node still marked `unsplit`; I set `status` to `split` and replaced step 2 with the same argument in fewer than 2000 characters. Its qcqs deduction is elementary from the three cited geometric statements; the remaining assertions are direct applications of the cited rational-category, ambient-membership and compactness statements. It hides no additional lemma. The existing logged Mathlib searches were read and reused; generic orthogonal and Verdier-localizing results do not state the item. No query was invented or rerun. The current shared and live node both show `status: unsplit`, despite a historical review, so this does not overwrite a currently completed split.
