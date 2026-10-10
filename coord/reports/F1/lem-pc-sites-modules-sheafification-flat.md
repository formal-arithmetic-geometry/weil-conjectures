Files written:

- `lem-pc-sites-modules-sheafification-flat.json` (repaired split; two new statement-only nodes; no Mathlib leaves).
- `lem-pc-sites-module-sheafification-interface.json` (statement-only Stacks site-level presheaf-ring interface; Mathlib generalization only).
- `lem-pc-sites-module-sheafification-tensor.json` (statement-only Stacks Tag 0GMW tensor/sheafification comparison; Mathlib generalization only).
- `citations.json` (verbatim quotes for every proof dependency used by every step).

Attachments: none. The abstract monoidal declaration `CategoryTheory.GrothendieckTopology.flat_presheafToSheaf_obj` remains non-applicable to the ringed-site statement.

WANTED: none.

The item follows Stacks Project `sites-modules.tex`, Lemma 18.28.3 (Tag 03ET). The returned version incorrectly used a topological-space module interface, applied the sheaf-of-rings exactness node to a presheaf ring, treated the tensor comparison as elementary, and asserted that the presheaf ring was already a sheaf. I repaired each point by adding the arbitrary-site interface node, citing underlying abelian sheaf exactness, adding Tag 0GMW as a node, and removing the false sentence.

## Not duplicates

- `lem-pc-sites-module-sheafification-interface` vs `lem-pc-presheaf-module-sheafification-ring`: the existing node is only for opens of a topological space, while the new node is for an arbitrary site and states the restriction-of-scalars adjunction for a presheaf ring.
- `lem-pc-sites-module-sheafification-tensor` vs `def-pur-sheaf-tensor-product`: the definition gives the tensor construction for a sheaf of rings; the new node compares that tensor over the sheafified presheaf ring with sheafification of the presheaf-ring tensor.
- `lem-pc-sites-module-sheafification-tensor` vs `lem-pc-presheaf-module-sheafification-ring`: the latter gives the module-sheafification interface, while Tag 0GMW gives the tensor comparison.
- `lem-pc-sites-module-sheafification-interface` vs `lem-weil-pbc-module-presheaf-sheafification-exact`: the existing node is for presheaves on the open subsets of a scheme with its fixed sheaf $\mathcal O_X$; the new node is for an arbitrary site and a genuinely presheaf ring $\mathcal O$.
- `lem-pc-sites-module-sheafification-interface` vs `lem-weil-pbc-sheaf-tensor-closed`: the existing node assumes a sheaf of rings and states monoidal closedness; the new node constructs the $\mathcal O^#$-module structure and restriction-of-scalars adjunction from a presheaf ring.
- `lem-pc-sites-module-sheafification-interface` vs `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`: the existing node is for a constant ring $R$ and ordinary $R$-module presheaves; the new node handles a variable presheaf of rings and semilinear module sheafification.
- `lem-pc-sites-module-sheafification-interface` vs `lem-pc-sheaf-modules-tensor-closed`: the existing node starts with a sheaf of rings and only gives tensor closedness; the new node gives the presheaf-ring-to-sheaf-ring module interface.
- `lem-pc-sites-module-sheafification-interface` vs `def-pur-sheaf-tensor-product`: the existing definition assumes $\mathcal O$ is a sheaf; the new statement applies when $\mathcal O$ is only a presheaf and identifies the induced $\mathcal O^#$-module category.
- `lem-pc-sites-module-sheafification-interface` vs `def-pur-presheaf-tensor-product`: the existing definition only defines sectionwise tensor; the new statement gives the sheafified module adjunction.
- `lem-pc-sites-module-sheafification-tensor` vs `lem-weil-pbc-free-sheaf-flat`: the existing item concerns flatness of a specific free sheaf and does not state the Tag 0GMW comparison for an arbitrary presheaf ring and arbitrary module.
- `lem-pc-sites-module-sheafification-tensor` vs `lem-weil-pbc-sheaf-tensor-closed`: the existing node assumes a sheaf of rings and its presheaf tensor is in a fixed coefficient category; the new node compares tensor over $\mathcal O^#$ with tensor over a presheaf $\mathcal O$.

## Review by F1

I reread the item source, Stacks Tag 03ET, and the cited tensor/sheafification source, Tag 0GMW (Lemma 18.26.2). I also read the statements of every existing node used by the repaired steps: `lem-weil-pbc-site-module-presheaf-sheafification-exact` supplies exactness of ordinary abelian module sheafification on an arbitrary site; `lem-weil-pbc-sheafification-exact` supplies finite-limit preservation by the sheaf inclusion and finite-colimit preservation by sheafification; `def-pur-sheaf-tensor-product` supplies the sheafified tensor construction; and `def-pc-flat-sheaf-modules` supplies the flatness criterion.

Step 1 now uses the new arbitrary-site presheaf-ring adjunction node for the actual scalar interface, then applies the two underlying abelian-sheaf finite-limit statements. The hypotheses match: $\mathcal O$ is only a presheaf, while $\mathcal O^#$ is the sheaf of rings used for the target module category. Step 2 cites the new Tag 0GMW node verbatim for the natural isomorphism $\mathcal G\otimes_{\mathcal O^#}\mathcal F^#\cong(\iota\mathcal G\otimes_{p,\mathcal O}\mathcal F)^#$, and the tensor definition identifies the right side with the composite from Step 1; this step is no longer marked elementary. Step 3 removes the incorrect claim that $\mathcal O$ is already a sheaf. It uses finite-colimit preservation of sheafification together with sectionwise right exactness of module tensor, then states the standard additive right-exact equivalence between finite-limit preservation and exactness before applying the flatness definition.

For both new nodes I searched the whole DAG and blueprint for the site-level interface and Tag 0GMW statement before creating them. I ran the required `leansearch`, `loogle`, `leanfinder`, and Mathlib `grep` searches; the two LeanSearch services were unavailable, and the records in `searches.jsonl` and the node `mathlib_searches` fields preserve that result. I checked the one-object identity-cover site, the zero module, and the unit module: sheafification is identity there and all comparisons reduce to the ordinary module tensor identities.

## Second reading by F1

The four returned points are repaired as follows: (1) the new interface node is arbitrary-site and presheaf-ring; (2) Step 1 uses the underlying abelian sheaf exactness and sheaf inclusion finite-limit nodes, not the sheaf-of-rings exactness node; (3) the new Tag 0GMW tensor node is cited by Step 2; (4) the false “$\mathcal O$ is already a sheaf” sentence is gone and Step 3 explicitly records the right-exact additive equivalence. The item, both new node statements, all step uses, and every citation quote were reread after these edits.

Step 1: checked against Stacks Tags 03CX/03CN/03CO and the cited ringed-site exactness statement; verdict: corrected the variable-presheaf-of-rings citation.
Step 2: checked against Tag 0GMW and the sectionwise tensor definition; verdict: the natural comparison has the required hypotheses and is non-elementary.
Step 3: checked against Tag 03ER and the flatness definition; verdict: conclusion is valid, but the right-exactness/finite-limits equivalence is theorem-level, so the step is marked non-elementary.
Node `lem-pc-sites-module-sheafification-interface`: checked against Section 03EK and all definition dependencies; verdict: self-contained arbitrary-site presheaf-ring interface.
Node `lem-pc-sites-module-sheafification-tensor`: checked against Tag 0GMW and the presheaf/sheaf tensor definitions; verdict: exact comparison statement, no Mathlib exact match.

Changes in this second reading: replaced the incorrect constant-ring exactness dependency with `lem-weil-pbc-ringed-site-module-sheafification-exact` and its exact quotation; changed Step 3's `elementary` flag to false because its categorical exactness criterion is not a two-line definition check; recorded these checks explicitly here.
