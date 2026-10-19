# Worker report: lem-per-projective-bundle-composition

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-projective-bundle-composition.json`: statement, split; unchanged statement, three complete proof steps following Stacks 0C4P.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-projective-bundle-relative-ample.json`: statement, unsplit; no Mathlib match. Stacks 07RL and the expanded definition 01VW(1).
- `dag/nodes/sec-deligne-laumon-a1/lem-per-quasiprojective-qc-composition.json`: statement, unsplit; no Mathlib match. Stacks 0C4M and the expanded definition 01VW(1).
- `dag/nodes/sec-deligne-laumon-a1/lem-per-proper-relative-ample-projective-bundle.json`: statement, unsplit; no Mathlib match. Stacks 0BCL(1), converse implication, and the expanded definition 01VW(1).

The sandbox also contains this report, citations.json (one verbatim statement per step/node citation), the retained searches.jsonl, and a sandbox-only generation script. No Lean was written or compiled. No shared repository or launcher file was changed.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact item tag, projective-bundle composition, IsProjectiveBundle, relative ampleness and quasi-projectivity found no declaration that states the item or any new helper with its general scheme hypotheses. `ProjectiveSpace/QuasiProjective.lean` restricts its predicate to a base field. `Modules/VeryAmple.lean:120-133` explicitly warns that its IsAmple predicate uses positive powers giving CLOSED embeddings into finite projective space over a field. Neither is the general relative-ampleness notion used here.

## WANTED

None. All mathematical sources used here are present in `literature/stacks-project/morphisms.tex`.

## Corrections and preserved work

The sandbox initially held searches.jsonl but no item copy, split, report or citations. I read and reused the earlier four actual searches, retained the item's inherited search records and imported fields, and added only the completed split and new searches. The earlier NOANSWER is not treated as a mathematical failure.

The item agrees with Stacks 0C4P (lemma-composition-projective), lines 10806-10823: the TARGET C is qcqs; f and g are projective in Definition 01W8(1), not assumed to embed into a finite projective space. No statement correction or dispute was needed. The former empty proof is now the source's complete argument. The three new nodes are general one-morphism conversion or quasi-projective composition inputs, not copies of the item's projective-composition conclusion.

The unit `sk-p-dl-a1-perverse` and chapter `sec-deligne-laumon-a1` were read. The current blueprint ancestor's proof is `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`. This item serves the existing normalized-blowup/desingularization branch recorded in blueprint.from; it is not the unit's key node. No unit fields or chapter route were changed. The new nodes carry the nearest ancestor lem-per-artin-gabber-affine-curve, the inherited exact projective-tower place supplemented by the subsidiary Stacks fact, and the inherited via list prefixed with this item.

## Mathlib and duplicate searches

All Mathlib searches were run with `/home/ubuntu/weil-launcher-nt/msearch.py Q01 lem-per-projective-bundle-composition`; the exact tool/query strings and actual hit summaries are recorded, including the four earlier searches. Each new node has leanfinder, loogle, grep and leansearch records; leanfinder and leansearch supply distinct phrasings. The item also has a second semantic phrasing and broader scheme-morphism grep. No search was invented. All services answered successfully; a loogle unknown identifier is recorded as the reported no-hit identifier result, not hidden as a theorem.

I read the returned types. Properness composition proves only properness; generic finite-type and quasi-compact composition do not supply an ample invertible module. `Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat` is properness of absolute Proj over an affine spectrum, not relative ampleness or projective-bundle composition over an arbitrary qcqs base (read Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:365-374). `Proj.fromOfGlobalSections` constructs a map but asserts none of the required relative-ampleness implications. The two broader grep hits are the Proj construction docstring (Scheme.lean:82) and a Weierstrass-curve coordinate map (EllipticCurve/Projective/Basic.lean:483); neither is a match. Loogle's IsProjective hits are categorical projective objects or projective measure families. Thus there are three new unsplit nodes and zero new Mathlib leaves.

I searched all DAG nodes by source labels, tags 07RL/0C4M/0BCL, and projective/quasi-projective/relative-ampleness wording; I searched the whole blueprint with blueprint_refs.py for projective, projective bundle, quasi-projective, relatively ample and each of the three tags, and verified the ancestor. No blueprint node states any of these three new general facts. I also searched the Lean source before creating the helpers. Existing lem-trf-projective-bundle-proper and lem-weil-pbc-proper-composition are reused, not duplicated.

## Not duplicates

lem-per-quasiprojective-qc-composition vs lem-per-quasiprojective-affine-composition: the existing node assumes a Noetherian affine final base and finite-projective-space immersions for both inputs, and concludes a finite-projective-space immersion; the new node treats arbitrary quasi-compact final bases and finite-type maps with relatively ample invertible modules. The existing special case cannot give the new general theorem.

lem-per-quasiprojective-qc-composition vs lem-per-excellent-quasiprojective-normalized-blowup: that node concerns normalization of an ordinary blowup over an excellent affine base; it neither assumes arbitrary composable quasi-projective maps nor asserts the general quasi-compact-base composition theorem.

lem-per-projective-bundle-relative-ample vs lem-trf-projective-bundle-proper: properness alone does not assert existence of a relatively ample invertible module, which is the new statement's essential content.

lem-per-proper-relative-ample-projective-bundle vs lem-trf-proper-fibrewise-ample-projective: the existing theorem assumes Noetherian schemes, fibres of dimension at most one and positivity on normalized fibre components; the new theorem has no dimension or Noetherian restriction and starts from relative ampleness. The fibrewise criterion cannot cover arbitrary qcqs bases or higher-dimensional fibres.

lem-per-projective-bundle-relative-ample vs lem-weil-pbc-projective-ample-invertible: the existing node assumes a closed immersion into a finite projective space over an affine ring and constructs its specific ample twist. The new theorem applies to projectivizations of arbitrary finite-type quasi-coherent modules over any scheme, so its arbitrary-base relative-ampleness assertion is not an instance of that affine theorem.

lem-per-projective-bundle-relative-ample vs lem-trf-algebraic-space-ample-local: the existing node descends an already specified line module and its ampleness from an etale cover. The new node obtains the existence of a relatively ample module from projective-bundle projectivity; its input does not supply any such etale-cover ampleness datum.

lem-per-projective-bundle-relative-ample vs lem-trf-scheme-ample-canonical-proj-criterion: the existing criterion assumes a specified invertible module and relates its relative ampleness to its canonical all-powers section-algebra Proj map. It does not assert relative ampleness of the pullback of O(1) along a closed immersion into P(E), which is needed for the new existence theorem.

lem-per-projective-bundle-relative-ample vs lem-trf-scheme-relative-ample-base-change: the existing theorem pulls back an already relatively ample module along a Cartesian base change. The new theorem constructs a relatively ample module from projectivity; no module with the required ampleness is an input.

lem-per-quasiprojective-qc-composition vs lem-weil-pbc-projective-ample-invertible: the existing theorem concerns the twist of a given closed immersion into finite projective space over an affine base. The new theorem treats two arbitrary composable finite-type morphisms with relatively ample modules over a quasi-compact base and needs no projective closed immersion.

lem-per-quasiprojective-qc-composition vs lem-trf-algebraic-space-ample-local: the existing theorem is an etale-local descent/representability criterion for a specified line module. It supplies neither existence of an ample module for a composite nor the tensor/pullback amplification argument used in 0C4M.

lem-per-quasiprojective-qc-composition vs lem-trf-scheme-ample-canonical-proj-criterion: the existing theorem is a characterization for one fixed morphism and one fixed module; it gives no implication producing a composite-relatively-ample module from two different relative-ampleness data.

lem-per-quasiprojective-qc-composition vs lem-trf-scheme-relative-ample-base-change: stability of relative ampleness under a Cartesian base change does not supply ampleness for composition; in particular f-pullback of a g-ample module need not by itself be ample for the composite.

lem-per-proper-relative-ample-projective-bundle vs lem-weil-pbc-projective-ample-invertible: the existing node starts with an actual finite-projective-space embedding over an affine ring and proves ampleness. The new theorem starts with properness and relative ampleness over a qcqs base and constructs projective-bundle projectivity, the converse direction with a more general base.

lem-per-proper-relative-ample-projective-bundle vs lem-trf-algebraic-space-ample-local: the existing node descends ampleness and scheme representability from an etale cover. It neither assumes properness nor concludes a finite-type projective-bundle embedding.

lem-per-proper-relative-ample-projective-bundle vs lem-trf-scheme-ample-canonical-proj-criterion: the canonical section-algebra Proj there may have an unbounded graded algebra; its criterion gives an OPEN immersion into that relative Proj. The new result requires properness and the qcqs finite-type approximation argument to obtain a CLOSED immersion into P(E) with E finite type.

lem-per-proper-relative-ample-projective-bundle vs lem-trf-scheme-relative-ample-base-change: the existing theorem preserves relative ampleness under base change, but asserts no projectivity criterion and constructs no finite-type quasi-coherent embedding module.

## Review by Q01

I read the source with the node files open. The item's statement is exactly morphisms.tex Tag 0C4P; its proof invokes 07RL, 01WC, 01W3, 0C4M, then 0BCL. Definition 01W8(1), lines 10487-10501, expressly permits any finite-type quasi-coherent E, not just locally free E. Definition 01VW(1), lines 9708-9721, says quasi-projective means finite type plus an f-relatively ample invertible module. Definition 01VH is expanded inline in each new node: quasi-compact morphism, and absolute ampleness on inverse images of every affine open of the target. The cited absolute-ampleness, invertible-module and finite-type definition nodes were read and give these precise notions. Thus no extra general quasi-projectivity definition node is needed.

For the first new node I read Tag 07RL, lemma-projective-quasi-projective, lines 10686-10702. It has NO qcqs-base hypothesis. The supplied conclusion is its quasi-projectivity conclusion with 01VW(1) expanded. Its future proof uses pullback of O(1), very ample implies relatively ample for quasi-compact maps, and finite type from properness; those are substantive inputs, so I have not called this an elementary fact from the properness node. For the second new node I read 0C4M, lemma-composition-quasi-projective, lines 9755-9766, including its references to finite-type composition and 0C4K. This needs only quasi-compactness of S. The actual tensor/pullback amplification lemma 0C4K, lines 8888-8908, was also read to check why the assertion is not elementary. For the third new node I read 0BCL(1), lemma-projective-is-quasi-projective-proper, lines 10777-10803. This converse is for arbitrary qcqs S and does not impose Noetherianness. Properness already includes finite type, so existence of the relatively ample module supplies exactly the remaining quasi-projectivity hypothesis. Its argument uses the finite-type projective compactification from the immediately preceding lemma and closedness of the proper image. It is not a restatement of projective composition.

Step 1 uses lem-trf-projective-bundle-proper exactly for properness of both f and g and the new 07RL node exactly for finite type and the two relatively ample modules. I read both statements; neither requires any unproved property of the intermediate scheme B. No assumption on B has been silently added.

Step 2 uses lem-weil-pbc-proper-composition exactly for properness of the composite. This is already a Mathlib leaf. The other citation, lem-per-quasiprojective-qc-composition, gives precisely existence of a relatively ample module N and finite type for that composite, with X=A, Y=B, S=C. The hypothesis used here is C quasi-compact, which is in the original statement. Both f and g have the required finite type and module witnesses from Step 1. I do not use a proof of a cited node in place of its statement, nor merely quote a tag in place of a DAG citation.

Step 3 uses lem-per-proper-relative-ample-projective-bundle with h=g∘f and the N of Step 2. Its properness, relative ampleness, quasi-compact final base, and quasi-separated final base are all verified. Its conclusion has exactly the same finite-type quasi-coherent projective-bundle convention as the item. This step does not upgrade the result to the stronger H-projective convention.

Small cases checked for each new statement: X empty (and an empty final base, which forces X and Y empty) is allowed; the unique rank-one module on the empty scheme and vacuous ampleness make all three statements consistent. An identity map on any scheme is projective via P(O)=S, and O is relatively ample for that identity because every affine open has ample O; there is no unintended assertion of absolute ampleness on the whole arbitrary scheme. P(O^{n+1}) gives the usual projective-space case. A non-locally-free finite-type E remains allowed in the first and third statements. The second includes open quasi-projective nonproper schemes; properness is needed only at Step 3. The third is not applied to merely locally projective or merely fibrewise ample data. These checks avoid missing hypotheses or changing coefficient categories; no cohomological coefficient category appears here at all.

I checked B1-B10: every new node introduces all objects, states no proof or proof sketch, has no proof dependencies, cites definitions of every specialized notion (relative ampleness is fully written inline), uses single-escaped TeX, gives a verified Stacks tag and label, has the required actual searches and blueprint ancestry, and has no exact Lean attachment. C1-C8 were checked against every used statement as above; the sole off-unit non-leaf input is the generic projective-bundle-properness theorem and is declared in split_report.tool_uses. The proper-composition leaf needs no such declaration. D1-D5 were checked: the proof carries all the assembly; the helpers have independent, strictly different conclusions/hypotheses and no dependency on the item. E1-E7 were checked using the source hypotheses and edge cases described above. I corrected no source statement; the actual repair is filling the former empty proof and making its previously implicit quasi-projectivity inputs explicit. Each proof step has fewer than 2000 characters, so no long step hides an additional lemma. There is no SGA source, no alternate purity route, and no modification of a target statement.

## Unfinished work

None for this one-level split. The three new statement-only lemmas are deliberately left unsplit for later workers, as the stage-1 contract requires. The initial server review_split check passed. The first delivery dry run correctly requested explicit same-tag comparisons for the shared relative-ampleness definition Tag 01VH. I opened all four existing statements, found that none states any of the three new facts, and added all twelve pairwise explanations under Not duplicates. No mathematical node changed in this repair. The final dry-run and push results follow when completed.
