# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-split-perfect-tensor-kinjective.json`: repaired source attributions, dual retraction wording, and proof metadata.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-split-perfect-dual-hom-tensor.json`: repaired source attribution, explicit ranks and dual retractions, provenance, blueprint ancestry, audit metadata, and Mathlib search records.
- `citations.json`: verbatim citations for every proof-step use.

## Attachments

None. No sorry-free project declaration states the item.

## WANTED

None.

## What was wrong or incomplete

The returned review identified four repairs. The helper and item had incorrectly called Tag 0A96 a dual tensor-Hom corollary; 0A96 supplies only K-flat-to-K-injective Hom, so the duality source is now Tags 0FPR (sites-cohomology `example-dual`), 0FNY (sites-modules `example-dual`), and 0FNK (signed dual complex). The helper now binds each finite rank `N_r` and states the dual retraction as a retract of `R^{N_{-q}}`; the item proof uses this corrected statement. The helper now has `created.by`, `created.item`, `created.date`, `created.group`, both initial Lean audit records, and `blueprint.from.via` containing the item generation. Its Mathlib records include a genuine `CochainComplex.HomComplex` Loogle query and the unavailable LeanSearch attempt; the prior malformed Loogle result is removed.

## Review by NF

I reread the item, helper, parent blueprint node, chapter and unit records, and the source passages at sites-cohomology Tag 0FPR (line 12960), sites-modules Tag 0FNY (line 4886), and more-algebra Tag 0FNK (line 18462). These sources provide the dual construction, termwise finite-free duality, and signed dual-complex tensor-Hom identification. I separately reread Tag 06YQ for bounded-above flat K-flatness and Tag 0A96 for the Hom-from-K-flat-into-K-injective conclusion; the item now assigns each fact to the source that actually states it.

Step 1 uses `lem-pc-bounded-above-flat-kflat-site` for bounded-above flat complexes. I checked the finite-free retract argument directly: tensoring a short exact sequence with a retract of a finite free module is a retract of an exact finite direct sum, and dualizing `p_r i_r=1` gives maps exhibiting `(P^vee)^q` as a retract of `R^{N_{-q}}`; bounded support gives bounded-above dual support. Step 2 uses the helper's explicit signed natural isomorphism, whose statement now includes the finite ranks and corrected dual retractions. I checked its source and the nonzero-differential sign test. Step 3 uses `lem-pur-hom-kflat-into-kinjective` exactly for `Hom(P^vee,I)` and then transports K-injectivity across the helper isomorphism; no extra boundedness of `I` is assumed.

I reran the required whole-DAG and blueprint duplicate searches before retaining the helper. I ran the helper searches through `msearch.py`: LeanFinder for the dual tensor-Hom concept, valid Loogle for `CochainComplex.HomComplex`, Mathlib grep for strictly-perfect/split-projective tensor-Hom names, and LeanSearch, which returned service unavailable; the records preserve those exact queries and outcomes. Small cases checked include zero, degree-zero finite projective, shifted free, and a two-term complex with nonzero differential. The helper remains statement-only and is strictly smaller than the item.

## Not duplicates

lem-weil-pbc-split-perfect-dual-hom-tensor vs lem-weil-pbc-split-perfect-tensor-kinjective: the helper states dual finite-free retractions and a chain-level tensor-Hom isomorphism; the item concludes K-injectivity.
lem-weil-pbc-split-perfect-dual-hom-tensor vs lem-pc-perfect-tensor-hom-duality: the existing node is a different perfect-complex route with its own hypotheses; the helper applies to an arbitrary small ringed site and explicit global retract data.

## Second reading by NF

- Step 1 (repaired numbering): checked against `def-pur-hom-complex`, 0FPR `sites-cohomology-example-dual`, and 0FNK `more-algebra-lemma-left-dual-complex`; the differential is explicitly $(-1)^{q+1}$ times precomposition, and the retraction composites are identities. PASS.
- Step 2: checked against `def-pc-flat-sheaf-modules` and the finite-free retract calculation of 0FNY `sites-modules-example-dual`; exactness of finite sums and their split summands gives flatness in a few lines. PASS.
- Step 3: opened `lem-pc-bounded-above-flat-kflat-site` and 06YQ `sites-cohomology-lemma-bounded-flat-K-flat`; its statement applies to D on this site with the boundedness and flatness established above. PASS. The existing node's source field says 06YS, but the local Stacks tags table assigns this label to 06YQ; this unrelated-node metadata error is reported here, not edited.
- Step 4: checked coordinate evaluation and both inverse equations against the definitions of sheaf Hom, sheaf tensor and complex totalization, and the finite-free/summand calculation in 0FNY and 0FPR. Restrictions preserve the coordinate formulas; finite support removes the infinite-product issue even for unbounded I. PASS, elementary.
- Step 5: expanded the Hom differential using its cited definition and the total differential using its cited definition; checked the two nonzero components, including the $(-1)^r$ evaluation correction and the $(-1)^{a+r+1}$ vertical coefficient, against 0FNK. PASS, elementary.
- Step 6: opened `lem-pur-hom-kflat-into-kinjective` and 0A96 `sites-cohomology-lemma-RHom-from-K-flat-into-K-injective`; both hypotheses apply to D and I. Checked the explicit transferred null homotopy against `def-pur-kinjective-complex`. PASS.
- New node `lem-weil-pbc-split-perfect-dual-hom-tensor`: checked against 0FPR, 0FNY, 0FNK and the existing site-level finite-projective evaluation statement. The statement was true, but its argument is elementary after writing the coordinate inverse and differential calculation; REMOVED under B1/C2 and the second-reader instruction to fold elementary helpers into steps. No new nodes or Mathlib leaves remain.

The item statement is unchanged. Its arbitrary small ringed site, commutative coefficients, globally split finite-free terms, finite support, unbounded I and nonzero d_P were checked individually against the route. The parent blueprint `lemma-weil-pbc-projection-formula-totalization`, chapter and unit records were opened; the proof still supplies the parent's K-injective tensor representative. No master sorry declaration is used as proof. The read-only slopmaster2 node-id and tensor/K-injective keyword searches found no matching declaration.

Small cases: P=0 or I=0 yields the zero total and Hom complexes; N_r=0 yields empty coordinate sums and P^r=0; P=R[0] gives the identity; over a field, P=R in any one degree gives the shifted I with the explicit evaluation sign. For P=[R --1--> R] in degrees 0 and 1 the dual differential from -1 to 0 is +1, and the two components in Step 5 give the same signed differential. On the empty scheme site all sheaves here are zero and the construction still applies.

Independent duplicate checks: whole-DAG source-tag search for 0FPR/0FNY/0FNK found no existing node with these tags; whole-DAG statements containing site, dual and Hom were read, including `lem-pc-bounded-ordinary-evaluation-assembly` (scheme/open hypotheses), and `lem-pc-finite-projective-internal-hom-evaluation` (termwise evaluation, no complex differential). Whole-blueprint searches for “dual tensor” and “Hom complex” yielded respectively none and only the K-injective definition bridge. The blueprint ancestor tool confirmed `lemma-weil-pbc-projection-formula-totalization`. Since the helper is removed, no new theorem duplicates an existing node.

Independent Mathlib searches were run with msearch.py and retained in searches.jsonl: LeanFinder “Evaluation isomorphism for a dualizable bounded chain complex: tensor with the dual equals the internal Hom complex” returned double-complex evaluation, ModuleCat coevaluation, a unitor, FGModuleCat duality and rigid-category infrastructure, none an exact site-complex result; Loogle '"dual", "HomComplex"' returned zero hits; Mathlib grep 'dual.*tensor|tensor.*dual|ihom.*iso' under Algebra/Homology returned zero hits. No match was promoted to a leaf.

Changes: removed the elementary helper and replaced its uses with explicit dual retractions, coordinate inverse equations, finite-support assembly and the signed chain-map calculation; stated the dual's K-flatness as its own explicit step; replaced the final isomorphism-invariance assertion by the transferred null homotopy; regenerated all citation quotes verbatim from the statements actually used. The first worker's sections are preserved as the history of the earlier split; their helper-file descriptions are superseded by this second reading.
