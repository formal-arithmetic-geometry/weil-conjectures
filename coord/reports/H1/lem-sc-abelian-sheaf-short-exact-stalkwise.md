1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-abelian-sheaf-short-exact-stalkwise.json`: statement node, split; no Mathlib match for the complete short-exact criterion.
- `dag/nodes/sec-curve-estimates/lem-sc-abelian-sheaf-exact-iff-stalk-exact.json`: statement node, Mathlib leaf via `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`.
- `dag/nodes/sec-curve-estimates/lem-sc-abelian-sheaf-mono-iff-stalk-mono.json`: statement node, Mathlib leaf via `TopCat.Presheaf.mono_iff_stalk_mono`.
- `dag/nodes/sec-curve-estimates/lem-sc-abelian-sheaf-epi-iff-stalk-epi.json`: statement-only node; the Mathlib local-surjectivity results are a generalization but do not package the abelian-sheaf specialization in one declaration.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. I checked the statement against the existing definition of abelian-sheaf cohomology and the Stacks exactness-at-points results. The middle exactness and left monomorphism claims are precisely the Mathlib stalk criteria recorded in the two leaf nodes. The right epimorphism claim requires the local lifting argument for sheaves; I recorded its exact stalkwise statement as a new unsplit node rather than claiming the Type-valued sheaf theorem is already the same abelian-category theorem. The item proof then uses the definition of `ShortExact` and applies all three criteria in both directions. The small edge cases checked are the zero maps and the constant zero sequence: all stalk tests reduce to the corresponding abelian-group tests.

## Review by H1

I read the assigned node, its `lean_audit`, the chapter and unit records, and the relevant source declarations in Mathlib `Topology/Sheaves/Abelian.lean` and `Topology/Sheaves/Stalks.lean`. I also searched the full DAG and blueprint for exactness, monomorphism, and epimorphism stalk criteria; the existing sets-valued epi node does not state the needed abelian-category conclusion, so it was not substituted. Step 1 cites the existing abelian-sheaf category definition for the ambient notion. Step 2 cites the exactness, monomorphism, and epimorphism criteria, and each cited node says exactly the criterion used. Step 3 cites the same criteria plus the ambient definition to reverse the implications. I verified every citation quote against the node statement and recorded all of them in `citations.json`. I corrected the imported empty proof by making the endpoint criteria explicit and by marking the epimorphism criterion unsplit where Mathlib only supplies its underlying local-surjectivity generalization.

5. Nothing remains unfinished in the split; the epimorphism criterion is intentionally queued as an unsplit statement node.
