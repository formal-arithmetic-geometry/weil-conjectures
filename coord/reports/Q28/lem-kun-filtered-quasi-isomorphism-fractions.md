## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-filtered-quasi-isomorphism-fractions.json`: statement, split in seven steps. Statement unchanged; no Mathlib match. All dependencies already exist.
- `citations.json`: a verbatim statement excerpt for every dependency used in every proof step.
- `report.md`: worker report and source review.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this auxiliary created node is not the unit's key node.

## Attachments

No attachment for the item. Searched the slopmaster2 project under `WeilConjectures/` for the blueprint id, filtered quasi-isomorphisms and filtered homotopies. The hits about cofiltered schemes concern different notions. There is no declaration giving this filtered fractions statement. The item has no `lean_audit` field or recorded declaration to inspect.

The proof uses the already attached `CochainComplex.mappingCone.quasiIso_iff_acyclic`, belonging to `lem-pur-quasi-iso-cone-acyclic`, in `WeilConjectures/Mathlib/Algebra/Homology/HomotopyCategory/Acyclic.lean:31` (read lines 15–40). Its statement is exactly the ordinary abelian-category cone criterion; its proof has no sorry, and the existing node's audit has slopmaster2 state `closed` with an empty open list. This is an existing finished tool, not a new attachment request or a Mathlib leaf.

## WANTED

None. The shared checkout omits the untracked literature payload, but the existing Stacks cache `/home/ubuntu/c1-stacks-review/` contains the sources. I read `derived.tex` there and the blueprint master node at `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f0f.md`. The canonical literature paths remain in the node.

## Corrections and route

The original statement is correct and is unchanged. Its proof was empty. The unit and chapter records were read. The historical ancestry leads to the projection formula's preliminary tensor-model comparison, through the integral tensor calculation and finite filtered K-flat replacement; the imported blueprint itself does not give an explicit fraction proof. I supplied the concrete module-level version of the source's cone-based MS2/MS3 argument and marked `proof_origin.by` as `agent`. I did not assert that a source triangulation theorem automatically restricts to this subcategory without proof. The constructions themselves establish the restriction to globally finite filtrations.

In particular, ordinary unfiltered quasi-isomorphism fraction calculus cannot simply be applied with filtered modules as an abelian category. Stacks explicitly says that finite filtered objects need not form an abelian category, and the desired weak equivalences are detected on every graded piece. This is why the ordinary Mathlib fractions instances are not a leaf for the item.

I searched the whole DAG and blueprint for filtered quasi-isomorphisms and fractions, using `tools/blueprint_refs.py search` and `ancestor`, and read the existing cone criterion and relevant definitions. No blueprint node states the item in another form, so `blueprint.same_as` remains empty. The ordinary cone criterion already supplies the only needed non-elementary input. The elementary acyclic-kernel projection calculation is proved inside step 3 rather than turned into a new node. No clause of the item was moved into a helper node.

## Mathlib searches

All additional searches recorded in the item were actually run with `/home/ubuntu/weil-launcher-nt/msearch.py Q28 lem-kun-filtered-quasi-isomorphism-fractions`; their tool/query pairs are in `searches.jsonl`. LeanFinder, Loogle, grep, and LeanSearch all responded successfully. A second LeanFinder phrasing about right Ore and cancellation returned ordinary cm5b and derived factorization/K-injective lemmas. I read `Mathlib/Algebra/Homology/DerivedCategory/Fractions.lean:26–40` and `Mathlib/CategoryTheory/Triangulated/Subcategory.lean:602–638`. The former assumes an abelian coefficient category and ordinary quasi-isomorphisms. The latter assumes a triangulated category and triangulated subcategory already constructed. Neither gives the current filtered category and graded equivalences by a one-line specialization. Existing historical search entries were preserved.

## Not duplicates

No new nodes were created, so there are no new/existing tag pairs to distinguish. The item is different from `lem-pc-quasi-isomorphisms-multiplicative-system` and `lem-pur-quasi-isos-saturated-triangulated`: those treat ordinary complexes in an abelian coefficient category. The current category has filtered maps and filtered homotopies and tests quasi-isomorphisms on all associated graded pieces.

## Review by Q28

I checked delivery-errors B–E against the written proof and the source, including the two frequent failures C1 and C4. For the item I read Stacks `derived.tex` at Tag 05RG, label `lemma-construct-multiplicative-system` (MS2/MS3 cone arguments); Tag 05RM, `lemma-acyclic-general`; and Tag 05S1, `lemma-filtered-acyclic` and its preceding definitions. I checked tags against the cache's `tags/tags`. I also read Tag 014E, `definition-cone`, to pin down the cone differential. Stacks allows filtrations finite separately in each cochain degree; the current statement asks for common bounds, so the final step verifies this stronger finiteness condition on the actual constructed objects. There are no new node sources to review.

1. Step 1 uses `def-sp-filtration` for filtration-preserving maps, `def-sp-filtered-complex-subquotients` for the quotients, and `def-weil-abstract-derived-category` for cohomology and quasi-isomorphisms. I opened all three statements. The homotopy identity descends to the quotient and differs by a boundary on cycles; thus homotopy invariance is proved here, not taken from a definition node. Identities, composition and two-out-of-three then follow from the written formulas for induced cohomology maps and inverses.
2. Step 2 uses these same three definitions. The derived-category definition actually writes the cone's matrix differential and shift, and the filtered-subquotients definition actually defines the graded complex. Grading is shown to commute with the specific cones and sums by the explicit direct-sum quotient map; no exactness assertion about the entire filtered-object category is assumed. Minimum lower bounds and maximum upper bounds are independent of cochain degree. Acyclicity of a shift is checked from cycles and boundaries.
3. Step 3 cites only the cohomology definition in `def-weil-abstract-derived-category`. I checked both parts of the cycle chase: the differential of a lift is in the kernel, and the corrected lift is closed; on the injectivity side, subtraction of a lifted boundary puts a closed element in the acyclic kernel. This is a few-line elementary argument for modules, not a hidden use of a long exact sequence theorem or a new unsplit lemma.
4. Step 4 cites the three definitions and `lem-pur-quasi-iso-cone-acyclic`. I read that node's full statement: it applies to arbitrary integer complexes in an abelian category, so it applies to each associated graded complex of R-modules with no boundedness assumption. The hypothesis is exactly the given graded quasi-isomorphism of s. The Ore differential squares to zero because f and s commute with differentials. The homotopy z has boundary ft-sg with the sign written. The kernel of the graded projection is the shifted cone of graded s, because the filtration is a direct sum; no unjustified exactness of grading on arbitrary filtered short exact sequences is used. Step 3 then proves t is in W.
5. Step 5 uses exactly the same four cited statements. Here sf=sg holds in the filtered homotopy category, so the available H preserves filtration, as needed; an unfiltered null-homotopy would not suffice. I checked d_C(a,-H)=(a d_X,d_Z H-sa)=(a d_X,-H d_X). The minus sign on H is essential. The projection q is a filtered chain map and qu=a on the nose. The ordinary cone criterion gives acyclicity of each graded C, not an unsupported claim of contractibility of C.
6. Step 6 cites the three definitions and refers to the already proved acyclicity and projection calculation in steps 5 and 3. The differential (d_X x,-d_C c-u x) squares to zero; k=-c gives d_C k+kD=ut. Thus qk=-y is the required filtered homotopy for (f-g)t. I expanded the differential into X,Y,Z coordinates to check the two minus signs and the +H term independently. The kernel of the graded t is a shift of graded C and is acyclic, so the denominator is a graded quasi-isomorphism, not merely an ordinary quasi-isomorphism. These are direct calculations from earlier steps, hence no additional non-elementary lemma is hidden.
7. Step 7 cites `def-sp-filtration`, whose statement supplies decreasing and finite filtrations. I checked explicitly that min/max of the three input bounds work simultaneously in all cochain degrees, also for the twice-shifted Z summand. The proof uses only three summands in each constructed degree and no degree truncation. It therefore proves the last clause of the item as well as both fraction axioms.

Small-case checks: zero complexes and the zero ring give the zero construction and no exceptional indices; s=id gives an acyclic (indeed contractible) kernel in the Ore construction; f=g permits H=0 and the cancellation formulas still work; if s=0 belongs to W, both its graded source and target are acyclic by the ordinary cone criterion, and the same construction does not divide by s. Changing or enlarging filtration bounds changes no formula. Unbounded input complexes cause no infinite direct sum, and a one-step filtration recovers the familiar ordinary complex construction. No false statement, missing hypothesis or type mismatch was found.

The only off-unit statement used is already Lean-closed (`lem-pur-quasi-iso-cone-acyclic`), so it is a permitted finished tool without a new route exception. Every cited node's statement is quoted verbatim in `citations.json`; no proof of a dependency or property of a definition was silently cited as its statement. The only repairs made were to the initially empty proof: the homotopy and kernel computations are now explicit. Nothing remains unfinished before the dry run.

## Second reading by Q28

I reread the item statement against Stacks Tags 05S1, 05RM, and 05RG in the cached `derived.tex`, and checked every hypothesis, the globally finite filtration clause, and the zero and one-step filtration cases; the statement is faithful and unchanged.

- Step 1: checked the induced graded maps and filtered homotopy calculation against `def-sp-filtration`, `def-sp-filtered-complex-subquotients`, and `def-weil-abstract-derived-category`; the identity, composition, and two-out-of-three argument is explicit and elementary.
- Step 2: checked the cone, shift, finite-sum filtrations, and direct-sum quotient identification against the three cited definitions; the common bounds are independent of cochain degree and no abelianity of filtered objects is assumed.
- Step 3: checked the degreewise-surjective acyclic-kernel cycle chase on zero and nonzero module complexes; both cohomology surjectivity and injectivity are proved in the displayed few-line calculation.
- Step 4: checked the Ore object, signs, filtered homotopy, graded cone kernel, and use of `lem-pur-quasi-iso-cone-acyclic`; its hypotheses apply to each graded complex, and step 3 supplies the projection quasi-isomorphism.
- Step 5: checked that equality in the filtered homotopy category supplies a filtration-preserving `H`, that `u=(f-g,-H)` is a chain map, and that the graded cone is acyclic; no unfiltered homotopy is used.
- Step 6: checked the shifted-cone differential, both minus signs, the homotopy `qk`, and the graded kernel calculation by expanding the $X,Y,Z$ coordinates; the cancellation denominator is in `W`.
- Step 7: checked minimum and maximum filtration bounds for every finite direct summand, including shifts, against `def-sp-filtration`; the constructions preserve global finiteness without truncating cochain degrees.
- New nodes: none; I searched the DAG and blueprint for duplicates and read the existing cone criterion, so no helper node or Mathlib leaf is warranted.

I found no statement, citation, source, or small-case defect requiring a change. The only change in this second reading is this audit section; the worker's explicit seven-step proof and citations remain intact. The dry-run preflight passes.
