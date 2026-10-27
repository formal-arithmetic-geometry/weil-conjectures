# Q20 stage-1 delivery: lem-sfb-field-groupoid-stabilizer-dimension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-stabilizer-dimension.json — existing statement, now split into four proof steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-constant-local-dimension.json — new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-connected-reduced-scalar-field-uniqueness.json — new statement-only node, unsplit; no Mathlib match.
- citations.json — one verbatim statement quote for every citation in every item step.

## Attachments

None. I searched lean/WeilConjectures/ for the item tag, groupoid/dimension, stabilizer/dimension and the supporting tags/concepts. The stabilizer hits concern discrete Galois/group actions, not this internal algebraic-space groupoid. No project declaration states the item or either new node exactly.

## Wanted

None. All sources used are in literature/stacks-project/.

## Corrections and limitations

The item statement is correct and unchanged. The chart dimension at a point is the infimum over neighbourhoods, not the Krull dimension of the local ring. This distinction is retained in the item and the constant-dimension node. The stabilizer written with (s,t), rather than the source's (t,s), is the same equalizer since the diagonal is invariant under swapping factors.

The inherited blueprint ancestry has from.node=null. The required ancestor command returns None. I retained it and the complete via list rather than inventing an ancestor. I read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof: paragraph (3) is direct-image preservation through proper/open factors. The inherited alteration/moduli chain is a supporting prerequisite, not text currently present as such in that paragraph. New from.place fields identify the exact uses in Stacks 06FF and retain that inherited chain; same_as is empty after whole-blueprint concept searches.

No Lean was written or compiled. No repository or launcher file was edited. The two new statements remain unsplit, as required for a one-level stage-1 split.

## Not duplicates

lem-sfb-connected-reduced-scalar-field-uniqueness vs lem-sfb-space-two-field-scalar-algebraicity: the existing statement only says the scalar images in a field-valued point are algebraic over each other; it does not identify integral closures in global sections or assert that they form a field. This proof needs precisely that stronger conclusion on a connected reduced scheme to compare scalar maps before reduction. The existing node allows arbitrary algebraic spaces with neither connectedness nor reducedness.

lem-sfb-connected-reduced-scalar-field-uniqueness vs lem-sfb-stack-universally-injective-point-lift: that existing statement is a lifting theorem for morphisms of algebraic stacks on geometric points; its 04MK reference records the scalar-algebraicity prerequisite, not the integral-closure equality for connected reduced schemes.

lem-sfb-field-groupoid-constant-local-dimension vs lem-sfb-quasiseparated-space-atlas-dimension: the existing node compares topological and chart dimension for quasi-separated spaces and the dimension of a surjective atlas; it does not assert that every point of a field groupoid has the same dimension, and assumes quasi-separatedness absent here.

lem-sfb-field-groupoid-constant-local-dimension vs lem-sfb-space-etale-atlas-topological-dimension: the existing node concerns dimension through an etale atlas after scheme base change for a quasi-separated morphism. It makes no groupoid homogeneity assertion and needs quasi-separatedness absent here.

lem-sfb-field-groupoid-constant-local-dimension vs lem-sfb-space-fibre-dimension-supremum: the existing node expresses fibre dimension as a supremum of chart dimensions; it does not make the dimensions at different points equal. The shared 04N5/04N6 tags are conventions, not the result 06FD/06FE.

The new constant-dimension node states local dimension is constant for one arrow space (and its group case). It does not mention a stabilizer and does not compare dimensions of two spaces, so it is not the item or a clause of the item. It is the strictly smaller independent input 06FD/06FE. Neither new node is an elementary two-line consequence of the cited definitions. The elementary nilradical/prime correspondence in the final step was kept as an explicit step, not made a node.

## Review by Q20

I read Stacks spaces-more-groupoids.tex, Situation situation-groupoid-on-field and the complete statements and proofs of 06FD, 06FE and 06FF. I also read varieties.tex at proposition-unique-base-field (04MK) and lemma-integral-closure-ground-field (04MI), and spaces-properties.tex at definition-dimension-at-point (04N5) and definition-dimension (04N6). Those are the sources of the item and each new node. The constant-dimension node extracts only 06FD(1) and its group specialization 06FE(1); the scalar node combines the equality of 04MK with the fieldness of 04MI, with nonemptiness explicit. These sources use no SGA.

Step 1 uses the affine-spectrum fibre-product formula to compute the stabilizer chart as the quotient by all scalar differences, not a merely set-theoretic equality locus. The source and target maps to U are finite type on an affine chart by the item's hypothesis and quasi-compactness. Quotienting preserves finite generation directly. The fibre-product/etale-cover node supplies the covering after base change, and the chartwise-etale permanence node supplies etaleness of its pullbacks. I read both statements: they actually assert base change of etale maps and covers. The scheme etale definition gives flatness and local finite presentation; composition is clause (e) of proper-fp-permanence, and the source-descent node explicitly assumes flat, locally finitely presented and surjective, all verified for the chosen disjoint union of chart covers. This prevents silently using finite-type permanence for algebraic spaces without a supporting statement. The group structure on the equalizer is pointwise restriction of the given groupoid operations, an elementary check.

Step 2 uses the new constant-dimension statement only for what it says: equality of global and point dimensions for R, and for the group groupoid of G after step 1 has established local finite type. The algebraic-space definition supplies an etale scheme chart through the identity. I read finite-type-component-open-qc: it assumes finite type over a field, which holds for both maps of the chosen affine chart. Its conclusion supplies an open connected component and finite type of that component; affine connected components are not assumed. The chartwise-etale permanence statement permits restriction to that open. I read reduction-universal-homeomorphism and the reduction definition: reducedness and the homeomorphism preserve the connectedness and nonemptiness, and quotient rings preserve finite generation locally for the two induced field structures.

Step 3 uses the full new scalar statement, not the weaker existing scalar-algebraicity node. Both locally finite type structures and nonempty connected reduced source were established in step 2. Equality of the residue-field maps at the identity is justified from the field-point equivalence in the cited algebraic-space point convention: equality after a common extension descends along an injective field map. The common integral closure is a field, so evaluation into the nonzero residue field is injective; this is the reason its fieldness matters. Then all scalar values agree in global sections. I read morphism-into-affine-scheme: its bijection applies to arbitrary scheme T, and consequently does not need T affine. Thus equality of global ring maps gives equality of the two morphisms. The fibre product universal property now gives the actual factorization into G.

Step 4 uses base change of etale charts, the affine spectrum's prime-ideal topology, and the reduction's nilradical quotient, all read in the cited statements. It spells out J contained in the nilradical on every affine open, so every prime contains J and the quotient has exactly the same underlying topology. The local homeomorphisms glue, giving the equality of the two point dimensions by correspondence of neighbourhoods and irreducible chains. This is elementary once steps 1 and 3 are available; no separate reduction/dimension theorem or unproved local-ring identity is smuggled in. The final equalities use the item's chart definition of dimension and step 2. Each non-elementary step is shorter than 2000 characters and uses only node statements, not constructions hidden in another node's proof.

For B1–B10, I verified the new nodes are self-contained statement-only nodes, with notions either cited or defined inline, TeX encoded once, precise Stacks tags and labels, actual recorded searches and no alleged Mathlib leaf. Whole-DAG tag and keyword searches and blueprint_refs searches were made before writing new nodes. I read the relevant existing statements rather than inferring their content from titles. The independent Mathlib searches for both new nodes each used two natural-language phrasings, Loogle, source grep and LeanSearch; all returned successfully. I read the hits: IsIntegralClosure.isField requires a domain already, whereas connected reduced schemes can be reducible; the global-field results in Proper.lean need universal closedness and an integral source, neither available here. Ordinary/manifold groupoids and smooth relative dimension do not prove the algebraic-space dimension statement. The item retained its imported searches and also received searches actually run by Q20.

For C1–C8 and D1–D5, I checked every uses entry against the full statement copied into citations.json, recorded generic off-unit scheme tools in split_report.tool_uses, and retained the source proof route. The steps prove the comparison; neither new statement restates it. For E1–E7 I checked all field, local finite type, connectedness, reducedness and identity hypotheses at their uses and explicitly computed the correct fibre product over U×_S U.

Small cases: the identity groupoid gives R=G=Spec K and dimension zero. A locally finite type group scheme gives s=t and the comparison is tautological. A constant finite group has several arrow components but constant local dimension zero, so the proof never assumes R connected. A finite Galois pair groupoid has nonidentity components not in G; the connected chart restriction is necessary, and the argument only compares near the identity. A purely inseparable finite pair groupoid can have nilpotents in R; the proof removes them through J contained in the nilradical, without claiming R=G as schemes. For the scalar lemma, a point with two different field automorphisms satisfies equality of the integral closures but not equality of the scalar maps: the item's extra equality at v is essential. A connected reduced reducible curve is allowed; this is why a domain theorem from Mathlib is insufficient. Disconnected reduced schemes can have a product of fields as their integral closure, and are deliberately excluded by the new scalar statement.

## Unfinished work

None within this split. The two new nodes intentionally enter the stage-1 queue as unsplit statements. Delivery validation and push results will be appended below.

## Validation

The required deliver.py --no-push invocation exited successfully and printed OK (not pushed) at 82aefde1850, with server preflight passed. This includes the server DAG and split-review checks. The final delivery command runs the same preflight before pushing.
