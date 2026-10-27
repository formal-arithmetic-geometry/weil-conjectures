# Stage-1 report: lem-sp-etale-counit-scalar-model

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-etale-counit-scalar-model.json: statement item, split into six steps using existing nodes; no Mathlib match for the entire assertion.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report. searches.jsonl is maintained by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained no item, report, citations or search log. The original item and its original searches were preserved; actual Q108 searches were appended, with their complete tool output records.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, common K-flat/counit/scalar names and the underlying notions. The hits concern other scalar counits or affine/stalk constructions, not this two-map ordinary-etale assertion. In particular a project theorem whose proof is sorry would not qualify.

## WANTED

None.

## Findings and changes

The imported item had a statement and search history but no proof. Its statement is retained verbatim: no additional boundedness of P, flatness of B/A or finite projective dimension was introduced. Its chapter and unit are unchanged. This is not the key statement node of the unit, so the unit realization record is not edited.

The exact derived sum counit is important. Identifying only source and target objects would not identify the actual maps. Steps 3 and 4 paste the representative-normalization squares for sigma, inverse scalar/pullback, and the actual localized counit. Step 5 uses naturality of scalar computation at the A-counit itself. The proof does not invoke the sheaf fold equality to deduce one identity from the other.

I found existing general nodes for all the auxiliary facts: notably lem-pur-etale-sum-flat-kflat and lem-weil-pbc-ringed-pullback-preserves-kflat. I therefore did not create separate flatness, bounded-resolution or comparison nodes. Off-unit generic tools are explained in split_report.tool_uses, for maintainer consideration, not installed as top-level tool_uses.

The original and current Mathlib searches found abstract derived adjunction lemmas, ordinary ring etaleness and ordinary module flatness. I read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean, especially derivedε and derivedε_fac_app, lines 118–130: they describe a general counit with given derived-factor hypotheses, not the etale common K-flat representatives and the specified scalar/sum maps. The second semantic query returned flat-module exactness and change-of-ring results, which neither give this sheaf comparison nor remove the need for its normalizations. Neither search result is an exact match or one-line specialization of the entire item.

## Unfinished work

No mathematical clause is left open in the split. The existing dependencies remain their owners' work. Server validation and delivery results are recorded below when available.

## Not duplicates

No new node was created. Whole-DAG statement/tag/concept searches and whole-blueprint searches for K-flat, sum extension and counit located the reusable nodes. The existing sum-extension K-flat theorem is deliberately cited rather than duplicated; the bounded compactification model lemma lem-sp-etale-sum-coefficient-computation is not used on arbitrary unbounded P.

## Review by Q108

I read the worker brief, stage-1 rules, the three-level route in SETUP.md, GOAL.md, the chapter and unit records and the current blueprint's exceptional-comparison proof, especially Charts. I read delivery-errors B through E in full. The source route here remains integral summation followed by canonical derived scalar computation. I used no SGA source. No Lean file, repository file, launcher file, compiler or build was changed or run.

For the item I read Stacks sites-cohomology.tex, lemma-pullback-K-flat (0G7E), lemma-K-flat-resolution (06YS), lemma-derived-base-change (06YY) and its proof. I also read derived.tex lemma-find-existence-computes (06XN) and lemma-right-derived-exact-functor (015F), and etale-cohomology.tex definition-extension-zero (03S3), the extension presheaf formula, its adjunction exercise and proposition-describe-jshriek (03S5). In sites-modules.tex I read lemma-j-shriek-and-tensor (0E8I) and lemma-j-shriek-flat (03EV). The latter directly covers the extended unit sheaf, not every flat sheaf; the general flat/K-flat preservation is taken from the full existing statement lem-pur-etale-sum-flat-kflat, not falsely attributed to 03EV alone. There are no new-node sources to review.

Step 1 uses the complete statements of lem-weil-pbc-ringed-pullback-preserves-kflat and lem-pur-etale-sum-flat-kflat. Both allow unbounded complexes and arbitrary commutative coefficients, and both state flat terms as well as K-flatness. The geometric pullback has exactly the constant-ring structural morphism required; e satisfies all the sum theorem's separated etale finite-type hypotheses. This proves preservation for the given P, rather than substituting a bounded P.

Step 2 uses the exactness clauses of lem-amb-etale-adjoint-locality and prop-weil-pbc-inverse-image-modules-exact, then the natural exact localization factor of lem-weil-pbc-exact-functor-derived-factorization. I checked the last node's final sentence says every termwise complex represents the derived image. Lem-pur-derived-change-of-rings supplies computation on K-flat complexes and canonical resolution compatibility. Its formula has direction T(QC) to Q(C tensor B); lambda and tau use its inverse and then T applied to eta, so their domains and codomains are the ones in the item.

Step 3 uses the actual statement of lem-sp-et-proet-coefficient-compatibility: sigma is expressly the summandwise tensor identification computed on a K-flat representative. Only that final clause is used, not its compactification or pro-etale coherence conclusions. The input H represents e* K, which the item's explicit hypothesis places in the permitted bounded constructible finite-Tor class. I checked def-pur-etale-scalar-pullback-iso's displayed normalization: its ordinary map goes in the reverse direction to the item's a-zero. Inverting the normalization gives the displayed square with a-zero; all cancellations are through invertible K-flat computation maps. Lem-sp-etale-sheaf-fold-scalar states exactly the generators and direction of rho and a-zero. This is an elementary use of specified normalizations, not a new comparison theorem.

Step 4 uses that same node's actual sheaf adjunction and its counit, and def-weil-exact-derived-adjunction's explicit sentence that units and counits are the localized originals. I wrote the counit naturality equation at r_P and the resulting composite, including the cancellation of the two H computation maps. Thus the cited definition supplies the specified map by definition; it is not being asked for an external theorem. The application does not use the fold/tensor equality, preserving the separate-identification character of this item.

Step 5 uses the same derived-counit normalization and natural scalar computation from lem-pur-derived-change-of-rings. Here v_A-zero is an actual chain map J to P between the K-flat complexes verified in Step 1. The naturality equation identifies Q(g_P), not an unspecified isomorphic arrow. No exactness of ordinary tensor with B is claimed.

Step 6 uses the explicit natural chain maps from lem-sp-etale-sheaf-fold-scalar and the canonical resolution compatibility in lem-pur-derived-change-of-rings. I wrote both chain-map naturality equations. For a general eta, both composites are natural transformations in K, so source transport is T(E e* eta) and target transport is T(eta); these are exactly the factors already in lambda and tau. Independent resolutions yield the same fixed derived morphism using the canonical scalar computation comparisons; no unsupported claim of a direct chain map between any two resolutions is made. Naturality of sigma, a and v is part of their specified natural-transformation data from Step 3 and the adjunction.

I tested e=id, where all comparisons reduce to ordinary scalar computation and the counit is identity; e with empty source, where J and both chain maps are zero; a finite disjoint union of copies of V, where everything is the finite-sum fold; the zero complex; and a nonflat quotient Z/ell^2 to F_ell. In the last test tensor on arbitrary complexes is not exact, but every use here is on the K-flat endpoints with natural representative maps. This is why neither B-flatness nor a bound on its projective dimension is needed. The proof also allows unbounded flat-term K-flat P even when its represented K is bounded.

For B1–B10 there are no new nodes, no hidden proof in a new statement, and no purported Mathlib leaf; the item's source, statement, blueprint origin and original searches were preserved. For C1–C8 I opened every cited node's statement and checked the quoted part against the inference, recorded every use in citations.json, and declared generic off-unit tools. No new edge is directed at the parent lem-sp-etale-sum-counit-scalar. For D1–D5 the steps themselves contain the map calculation rather than relabeling clauses as nodes. For E1–E7 the tests above include empty and nonflat cases, every comparison has its checked direction, and the compatibility and transport equations are written. Every step is shorter than 2000 characters; none conceals a separately stated sublemma.
