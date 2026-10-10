Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-truncation-kernel-flat.json`: item, statement split; no new nodes; Mathlib searches found no match.
- `citations.json`: verbatim citations for the two non-elementary uses.

Attachments: none.

WANTED: none.

The item was not present as a declaration in `WeilConjectures/`, and no duplicate statement was found in the DAG or blueprint. I read the parent node `lem-sc-affine-truncation-kernel-finite-locally-free` and the related `lem-sc-affine-perfect-plus-locally-free`; both use this item exactly for the localized image module. I checked the item statement against Stacks Tag 08ED's last-one-flat paragraph. The hypotheses used in the proof are the affine scheme, quasi-compact open, bounded-above finite-free complex, lower Tor bound `r<a`, and a principal open `D(f)` contained in `U`.

## Review by H1

I read the Tag 08ED proof location named by the item and verified that the conclusion is module-level: for each `f` with `D(f) ⊆ U`, the localization of the lower image is flat and finitely presented. Step 1 cites the existing affine Tor-amplitude criterion, whose statement explicitly supplies vanishing of the localized derived tensor complex for every module in degrees below `a`. Step 2 is elementary finite-presentation bookkeeping from the finite free presentation of the image. Step 3 uses the cited Tor-amplitude vanishing in degrees `r-1` and `r` to identify the tensor kernel and apply the tensor criterion for flatness; the finite-free terms provide the required presentations. Step 4 is the localization-to-sheaf conclusion and is elementary. I checked the edge cases `P=0` and `r=a-1`; both reduce to the zero module or the same two-degree vanishing argument. The three required Mathlib searches were run with the item id and recorded in the node; LeanFinder returned only unrelated projective-dimension results, Loogle returned no hits, and the Mathlib grep returned no hits.

What I could not finish: none.

## Second reading by H1

- Statement: checked hypothesis by hypothesis against Stacks Tag 08ED (the last-one-flat paragraph); the affine, quasi-compact-open, bounded-above finite-free, Tor interval, `r<a`, and principal-open quantifiers agree. The zero complex, a field, the empty open, and `r=a-1` give the stated zero or ordinary flat modules.
- Step 1: checked against Tag 08ED and `lem-pc-affine-tor-amplitude-criterion`; localization to `D(f)` preserves the displayed tensor complex and its cohomology, after which the affine criterion gives the module vanishing.
- Step 2: checked against the finite-free presentation in Tag 08ED; the displayed map from `P_f^{r-2}` supplies finitely many relations, so the finite-presentation claim is elementary.
- Step 3: checked against the tensor exactness argument in Tag 08ED and the existing `lem-pc-module-flat-opcycles-tor-criterion`; its hypotheses hold because the localized terms are finite free and `H^{r-1}` vanishes. The `H^r` vanishing gives the exact kernel-cokernel sequence, and flatness of its two right terms gives flatness of `K_f` by the tensor criterion.
- Step 4: checked against the conclusion of Tag 08ED; the principal-open and quasi-coherent sheaf formulations are equivalent by localization.

Changes: repaired step 3 with the existing opcycles flatness node and updated `proof_deps` and `citations.json` with its verbatim statement. No new nodes were needed.
