1. Files written: `dag/nodes/sec-smooth-purity/lem-kun-cp-approximation.json` (statement, split); `dag/nodes/sec-smooth-purity/lem-kun-etale-residue-field-finite.json` (statement-only, no Mathlib match); `citations.json`.
2. Attachments: none.
3. WANTED: none.
4. The returned node had an unrestricted definition of “finitely generated”, and its Step 2 incorrectly claimed that the image of a closed support upstairs is closed in X. I repaired the definition to finite families of sections on affine (quasi-compact) etale charts, following the Tag 03SA extension-by-zero construction. Step 2 now proves finiteness upstairs: the section support is closed in the affine chart, points over closed points of X have finite residue fields, the chart is finite type over K, and the finite support maps to X. The prior unsupported `def-weil-pbc-etale-sheaves` citation remains absent; the stalk inclusion is elementary from the subsheaf definition. Existing DAG statements were read in full for every citation.
## Review by M1

Step 1 constructs the filtered system of finite-generator subsheaves, verifies filteredness by sums, and checks the colimit map sectionwise; it uses no non-elementary statement. Step 2 uses the support definition and the geometric-point independence lemma to identify the cyclic support, then applies the finite-closed-subscheme statement after the elementary subsheaf-stalk inclusion. Step 3 uses the finite union of cyclic supports and the essential-image clause of `lem-kun-04ca` to obtain the closed-immersion pushforward description. I verified that each citation quote is copied from the cited node statement and that all hypotheses (finite type over a separably closed field, support in closed points, reduced finite closed subscheme) occur in the item or the cited statements. The Mathlib searches found no matching sheaf approximation theorem; LeanSearch was unavailable and recorded as such.

## Second reading by M1

- Item statement: checked hypothesis by hypothesis against Stacks Tag 0F0N (`lemma-support-in-subset`), part (2), specialized to a finite-type scheme over the separably closed field and the closed-point specialization-closed set; the support, finite-support, and reduced closed-immersion conclusions agree.
- Step 1: checked the filtered index of finitely generated subsheaves, the sum refinement, and the sectionwise colimit argument; the step is elementary from subsheaf and filtered-colimit definitions.
- Step 2: checked the support and geometric-point citations, plus `lem-kun-etale-lfp` and `lem-kun-closed-point-field`, against their complete node statements. The support is handled upstairs on the affine etale chart and only then mapped to X, avoiding the returned false closed-image inference; the finite-set conclusion matches `lem-kun-finite-closed-subscheme`.
- Step 3: checked the finite union argument and the essential-image clause of `lem-kun-04ca`; its cited statement gives exactly the pushforward characterization used.
- Node audit: the proposed `lem-kun-etale-residue-field-finite` was removed as a duplicate of the existing Mathlib-backed `lem-weil-pbc-etale-residue-field-extension-separable`; the latter was checked for exact scope and cited instead. No new node remains, so B1-B7 and new-node search checks are vacuous.
- Edge cases: the zero sheaf has the empty filtered support and empty reduced subscheme; for a field or a finite discrete scheme the support is finite and the assertion reduces to the usual finite union of skyscraper subsheaves; the empty scheme is vacuous. No parameter `n` occurs in this item, so the n=0 and n=1 checks are inapplicable.
- Changes made: corrected the Stacks source location to the labeled Lemma 0F0N, removed the duplicate residue-field node, made the finite-presentation-to-finite-extension argument explicit in Step 2, updated citations, and recorded this review; dry run rerun below.
- Final dry run: `python3 /home/ubuntu/weil-launcher/deliver.py M1 lem-kun-cp-approximation --no-push` passed at `bc3a39b47`.

## Not duplicates

lem-kun-etale-residue-field-finite vs lem-weil-pbc-closed-point-residue-field-base: the new node concerns finite separable residue extensions along an arbitrary etale morphism, while the existing node concerns finiteness of the residue field of a closed point over an algebraically closed base.
