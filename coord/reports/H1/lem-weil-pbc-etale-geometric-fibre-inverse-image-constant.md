1. Files written:

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-geometric-fibre-inverse-image-constant.json`: split item, no Mathlib leaf.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant.json`: new statement-only node, no Mathlib leaf.
   - `citations.json`: verbatim statement excerpts for every step citation.

2. Attachments: none.

3. WANTED: none.

4. What was checked and changed: the item was not stated by any sorry-free declaration in the slopmaster2 source, and its existing statement agrees with Stacks Tag 0A3H (Lemma 59.39.3), final paragraph. I searched the whole DAG and blueprint for the algebraically closed-field constancy fact and found no existing node. The split follows the source paragraph: Step 1 applies the new statement that every sheaf on $(\\operatorname{Spec}\\Omega)_{\\Et}$ is canonically constant with value its global sections; Step 2 uses its identity-point stalk clause and the existing set-valued inverse-image stalk-germ statement (Stacks Tag 03Q1) to identify that value with $F_{\\bar s}$; Step 3 checks naturality using the same two statements and the existing composition/unit compatibility node. Each cited node was opened and its quoted sentence says exactly the fact used. I checked the edge cases $U=\\operatorname{Spec}\\Omega$, $U=\\emptyset$, and identity pullback: the constant-sheaf map is respectively the identity on global sections, has the unique empty section, and is natural. Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) were run for both the item and the new node; LeanSearch was unavailable and recorded as such.

## Review by H1

I read the imported item source and the Stacks Tag 0A3H final paragraph, then read the full statements of `lem-weil-pbc-sets-etale-inverse-image-stalk-germ` and `lem-weil-pbc-sets-etale-inverse-image-composition-units`. Step 1 uses only the new node's constancy statement. Step 2 uses the new node's identity-stalk clause and the existing stalk-germ node's bijection, including its explicit germ formula. Step 3 uses the naturality clause of the new node, the existing stalk-germ node's global-section compatibility, and the existing composition/unit statement. The hypotheses match: $\\Omega$ is the algebraically closed field of the geometric point, $F$ is a sheaf of sets on $S_{\\Et}$, and $U$ is an arbitrary $\\Omega$-scheme. I corrected the split to keep the algebraically closed-field equivalence as a statement-only dependency rather than hiding it in an elementary step, and recorded all citations verbatim in `citations.json`.

5. What could not be finished: no Lean implementation was attempted, per stage-1 rules.
