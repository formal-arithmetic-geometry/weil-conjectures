1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-sections-fpqc-descent.json` (statement, split)
- `lem-weil-pbc-etale-sections-equal-open.json` (statement-only, no Mathlib match)
- `lem-weil-pbc-etale-open-fpqc-descent.json` (statement-only, no Mathlib match)
- `lem-weil-pbc-etale-inverse-image-section-description.json` (statement-only, no Mathlib match)

2. Attachments: none. No sorry-free Lean declaration states the item exactly.

3. WANTED: none. The local Stacks source read was `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`; the DAG source path is `literature/stacks-project/etale-cohomology.tex`.

4. The returned split was mathematically false: an fpqc family of maps need not generate a covering sieve in the small etale site. I deleted the generated-sieve node and followed Tag 09XN lines 4960-5020. The new nodes state exactly the three non-elementary ingredients used there: Tag 09XM's largest agreement open, Tag 03N0's fpqc descent of opens, and the local etale factorization description of inverse-image sections. The item now has four steps: form agreement opens, descend them, refine sections and form the opens (W_i), then glue the (t_i|W_i) over an etale covering. Every citation quote is copied from the cited node statement. I checked hypotheses on the small identity cover and on the singleton case; the latter reduces to the two projection condition with the existing inverse-image composition isomorphism.

## Review by G1

I read Tag 09XM (lemma-where-sections-are-equal) and Tag 09XN (lemma-describe-pullback), etale-cohomology.tex lines 4958-5027, plus Descent Tag 03N0 (descent-lemma-open-fpqc-covering). The item statement retains the arbitrary scheme, fpqc family, arbitrary small-etale sheaf, and the two projection identifications. Step 1 uses the exact largest-open statement from the 09XM node; step 2 uses the exact equal-open descent statement from the 03N0 node; step 3 uses the exact local inverse-image section statement and the two open statements; step 4 uses the sheaf equalizer definition and the existing inverse-image composition isomorphism. The three new nodes were searched against the DAG, blueprint, source tree, LeanSearch, LeanFinder/Loogle, and Mathlib grep; no existing node or Mathlib declaration states them. I corrected the prior false generated-sieve route, removed the generated-sieve node, and replaced the unfinished delivery notes with the actual source paths and lines read.
