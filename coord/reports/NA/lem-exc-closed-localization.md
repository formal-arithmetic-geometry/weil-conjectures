# Stage 1 report

1. Files written: `dag/nodes/sec-smooth-purity/lem-exc-closed-localization.json` (statement, split; Mathlib no match). No new nodes.
2. Attachments: none.
3. WANTED: none.
4. The imported proof had one long paragraph and omitted the declared pro-etale operations dependency. I split it into three complete steps and restored that dependency. The statement remains the blueprint statement. The first step uses the slice/evaluation statement and the sectionwise direct-image formula. The second uses the chosen cartesian inverse-image isomorphism and exact inverse image from the operations definition; generator and colimit extension are stated explicitly in the step. The third uses the sectionwise adjunction and the restriction comparison to identify unit and counit. Mathlib searches were run for the item and found no matching theorem.
5. Nothing remains unfinished.

## Review by NA

I read the item blueprint and the existing statements of `lem-weil-pbc-proetale-restriction-injectives`, `def-weil-pbc-cartesian-square`, and `def-weil-pbc-proetale-operations`. Step 1 uses exactly the slice identification and the direct-image evaluation formula, with the weakly etale hypothesis supplied by the former. Step 2 uses the cartesian square's specified inverse-image isomorphism and the operations node's exact inverse image; the reduction through free representables and cokernel presentations is written in the step. Step 3 uses the operations node's derived adjunction and the restriction node's evaluation comparison, while the cartesian node supplies naturality under pasted squares. I checked that every citation quote is verbatim from its node statement and that all proof dependencies are included. The item has no Lean declaration in the reference source, and its statement was unchanged.

## Second reading by NA

- Item statement: read the blueprint node at order 1846 and its unit; all weakly etale, closed immersion, direct-image, inverse-image, and adjunction clauses agree. Constant coefficient module convention is the cited site convention; no derived or completed coefficients are substituted.
- Step 1: opened restriction-injectives and operations statements; their slice and section formulas give exactly both displayed fiber products, arrows, and actions. Verdict: valid, notation and naturality made explicit.
- Step 2: opened the cartesian-square, proetale-inverse-image, restriction-injectives, and operations statements. Compared the defining comma colimit and base-change functor with proetale functoriality and sites inverse image, and module lifting with sites-modules.tex, lemma-adjoint-push-pull-modules. Verdict: replaced uncited free presentations by explicit inverse maps on comma-colimit representatives; projection and graph indexing arrows prove both composites are identities. No representable-generation result is needed.
- Step 3: opened inverse-image and operations statements and read the module-adjunction calculation at sites-modules.tex label lemma-adjoint-push-pull-modules. Verdict: replaced a derived-adjunction citation and vague sectionwise counit with the actual unit coprojection and counit restriction formula. The equality of restrictions is written on each colimit representative.
- New nodes: none, so B1–B7 and new-node Mathlib searches are vacuous. Searches for existing localization statements and presentation statements covered all DAG chapters; existing Lean source was searched by item ID and proetale square/localization vocabulary, with no exact closed declaration attached.
- Edge cases: zero module gives zero through colimits and sheafification; field coefficients obey the same scalar action; empty W or Z gives the empty slice and zero module sheaf; identity localization makes replacement and graph maps identities. No nonempty, finite-type, or injectivity hypothesis is used.

Changes: expanded step 1 notation; replaced step 2's uncited presentation theorem with the inverse-image definition's comma-index calculation; corrected step 3's unit and counit formulas and verified their compatibility on representatives; added the existing inverse-image definition dependency and regenerated verbatim citation quotes. Original worker sections are retained above.
