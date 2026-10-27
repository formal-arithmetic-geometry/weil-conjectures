## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-presentation-homology.json`: split the item in six steps; statement unchanged; Mathlib verdict no match.
- `citations.json`: one verbatim quotation for each step/node citation.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. Attachments: none. WANTED: none. Unfinished parts of this split: none; the cited general computation retains its own existing dependencies.

The original item had no proof and no split report. No previous sandbox item or report existed, and no repair note exists. I retained the original statement, source, chapter, unit, blueprint ancestry, creation record and earlier Mathlib search records, and appended the searches actually run in this session. I found no statement dispute. No Lean was written or compiled, and no repository or launcher file was changed.

## Sources and route

Read `literature/stacks-project/cotangent.tex`, Tag 08PS, label `lemma-identify-pi-shriek` (lines 229--278), and Tag 08QI, label `remark-resolution` (lines 667--708). The category in Stacks is opposite to the item's presentation category; its cosimplicial site object therefore becomes this simplicial object, and its presheaf becomes this covariant module functor. The generator-image description, the use of actual fibres over specified elements of B, and arbitrary products are exactly the proof of 08PS. The statement of 08QI confirms that resolutions have polynomial terms and a trivial Kan augmentation; it does not require presentations T to surject onto B.

Read `simplicial.tex`, definition `definition-trivial-kan`, and Tags 08NN (`lemma-trivial-kan-base-change`), 08NR (`lemma-product-trivial-kan`), 08NS (`lemma-trivial-kan-homotopy`), around lines 5530--5664. The base-change and product facts are elementary boundary-filler arguments and are written into step 3, not introduced as nodes.

Read `sites-cohomology.tex`, Tag 08Q9, label `lemma-compute-by-cosimplicial-resolution` (lines 10229--10300), including its double-complex proof. The existing node `lem-trf-simplicial-derived-colimit-computation` already states precisely its general small-category version, the projective-resolution definition, first-vertex bar convention, and stronger reindexing/scalar naturality. I read that node's complete statement and proof and its accepted review; I do not infer these extra clauses merely from 08Q9's abbreviated statement.

Read the recorded chapter and unit, and the current main-20261015 proof file for `lem-trf-local-term-locality`. The item's long inherited ancestry identifies it as an algebraic supporting input in that local-term branch, not a new assertion in the blueprint itself. Blueprint-wide searches for `contractible`, `derived colimit`, `polynomial presentation`, and `trivial Kan` found no blueprint statement of the item. I retained its exact inherited `from.place` and `via`; `same_as` remains empty. The split follows the polynomial-resolution route already named by its parent, with no SGA source.

## Existing-node and Lean searches

Searched the whole DAG by tags 08PS, 08QI, 08Q9, 08NN, 08NR, 08NS, and concepts including representable contractibility, derived colimit and trivial Kan fibrations. This found the existing general computation and homotopy-inverse nodes used here. Searches by item tag and polynomial-presentation/homology concepts under `lean/WeilConjectures/` found no project declaration proving this item, so no attachment is claimed. The existing stage-3 record on the homotopy-equivalence node is only information about that supporting result, not an attachment for our item.

## Mathlib searches

All four fresh queries are recorded verbatim by `msearch.py` in `searches.jsonl` and appended to the item's `mathlib_searches`:
- leanfinder: `derived colimit of a module valued functor computed by a simplicial object with contractible representable Hom simplicial sets`.
- loogle: `"derived", "colimit"`.
- grep: `derived.*colimit|colimit.*derived|polynomial.*simplicial`.
- leansearch (second phrasing): `homology of a small category computed by an augmented polynomial simplicial resolution`.

All services answered successfully. LeanFinder returned ordinary module/presheaf colimits, a Yoneda presentation, a monoid resolution, and Dold--Kan constructions. I read `Presheaf/Colimits.lean` lines 95--120 (`isColimitColimitCocone` at 114) and `Presheaf/Generator.lean` lines 190--213 (`isColimitFreeYonedaCoproductsCokernelCofork` at 203): they give ordinary colimits/presentations, not the asserted derived comparison. Loogle and grep returned `CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt.hasColimit`, `PointwiseRightDerived.lean` line 63, and the primed variant: I read lines 50--85, which give pointwise left Kan extensions of a localization under derived-functor hypotheses, not this computation. LeanSearch returned simplicial augmentation and homology definitions/instances. No hit states representable contractibility for polynomial presentations or the entire comparison. The general monoid bar resolution is restricted to a different index category. The whole item therefore remains a split, not a Mathlib leaf.

## Not duplicates

No new nodes. In particular I did not create separate nodes for either fibre stability or product stability of boundary lifting: the coordinatewise proofs are step 3. I reused `lem-trf-simplicial-derived-colimit-computation` instead of creating another resolution criterion or bar-comparison node.

## Review by Q68

I checked the six written steps against their sources and opened the statement of every node cited by them. This is the author's review for direct delivery.

Step 1 uses the size convention only for the containing universe and the simplicial-object definition only for the functor condition. Its smallness justification is explicit: ring structures and maps on underlying sets belonging to U form sets in V. Q's operators preserve the augmentation by the hypothesis of an augmented simplicial algebra, hence really are arrows of the category, not just algebra maps. The simplicial definition says exactly what is needed. Neither cited definition is used to assert a homological theorem.

Step 2 uses polynomial evaluation and finite support directly. In each degree the inverse map is evaluation on the generator tuple, and augmentation compatibility can be checked on generators because both maps fix A. This proves the simplicial isomorphism, including its compatibility with every operator, rather than just a degreewise bijection. It is elementary and needs no separate theorem node.

Step 3 uses precisely the degree-zero surjectivity and boundary lifting in `def-weil-pbc-trivial-kan-fibration`. For a fibre, the prescribed base simplex is the constant b, so the chosen filler still lies in that fibre. For the product, each coordinate has the specified boundary, and assembling coordinate fillers respects all operators. Set-indexed choice handles infinite E. These are the full elementary arguments of 08NN and 08NR; a bare tag is not being substituted for a missing proof citation.

Step 4 uses the actual conclusion of `lem-weil-pbc-trivial-kan-homotopy-equivalence`: a section g and a cylinder homotopy from the identity to g followed by projection. Its hypothesis is the trivial fibration proved in step 3. This node states a homotopy inverse, so there is no misuse of a mere weak-equivalence or fibration criterion. I declare this off-unit generic simplicial tool in `split_report.tool_uses`; no trace-formula-unit node replaces it.

Step 5 uses the full statement of `lem-trf-simplicial-derived-colimit-computation`. I checked smallness in V, the given commutative coefficient ring in V, covariance of F, and contractibility for every T (not merely finite-variable or surjective presentations). The node explicitly defines its derived colimit by projective resolutions in the functor category, gives the alternating-face complex, and specifies the first-vertex bar convention. Thus no uncited identification between two definitions of homology or sign conventions is needed. Its naturality in F is stated, not inferred from its proof.

Step 6 uses that same node's reindexing formula, with identity category functor, identity scalar map and identity coefficient transformation. Q' meets the contractibility hypothesis by the preceding argument applied to it. The augmented map h lies in the same presentation category. On every bar generator the resulting target map is literally the identity, so the general formula is precisely the requested equality. This also ensures the canonical comparison is used; choosing separate homotopy inverses for each Q is unnecessary.

Small cases checked: E empty gives Hom(A,Q) a singleton; E infinite still allows polynomial evaluation because each polynomial involves finitely many variables and boundary fillers are selected coordinatewise. Non-surjective T maps cause no problem: only the prescribed generator values need lifts, and the Q augmentation, not T's map, provides them. Zero coefficient ring and zero F give zero complexes on both sides. A polynomial B with constant Q=B and identity augmentation yields singleton representable Hom and the usual evaluation comparison. The zero ring B gives fibres over its single element; no nonzero-ring assumption was introduced. Identity h gives identity on the bar model, and compositions satisfy the same generator formula.

Checked B--E of delivery-errors: no new-node form or duplicate issue; every non-elementary inference cites a node whose statement supplies it; elementary filler arguments are written out; no clause is moved into a new restatement. No source error, hypothesis change, route change or hidden comparison remains. Dependency traversal from both cited theorem nodes found no path back to this item. Every proof step is below 2000 characters (618, 581, 787, 339, 580, 605). The citation quotations are literal substrings of the current statements, including the full comparison statement for steps 5 and 6. The dry run and final delivery results are recorded below when obtained.
