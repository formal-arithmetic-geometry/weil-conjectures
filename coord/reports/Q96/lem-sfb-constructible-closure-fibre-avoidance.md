# Stage-1 worker report: lem-sfb-constructible-closure-fibre-avoidance

Group Q96; direct delivery; 2026-10-24. Only the sandbox was written. No Lean was written or compiled, no Lake/build tool was run, no agent was started, and no repository or launcher file was changed.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-closure-fibre-avoidance.json`: item, statement unchanged, complete twelve-step split; not in Mathlib.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-residue-transcendence-dimension-bound.json`: new statement-only lemma, unsplit, no Mathlib match. This is the general, possibly reducible and nondominant, scheme dimension inequality of Stacks 0BAG.
- `citations.json`: one entry for every node used by every numbered item step; every quote is copied verbatim from that node's statement. Whole statements are quoted where this avoids omitting hypotheses of the application.
- `report.md`: this report. `searches.jsonl`, the captured `item-*.txt`/`generic-*.txt` search answers, and `write_split.py` are sandbox research records, not additional DAG nodes.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the closure/constructibility/fibre/dimension notions. The constructible-module selection and deformation-space closure declarations have different objects or conclusions. `WeilConjectures.AlgebraicGeometry.FiberDimension` proves a bound using the dimensions of all fibres; it does not state the generic-point transcendence bound or this item's assertion. I did not treat project declarations containing `sorry` as completed proofs.

## Wanted literature

WANTED: Deligne, *Le lemme de Gabber*, Astérisque 127 (1985), Lemma 4.6, printed p.144, for the item's final dimension-counting sentence. The locally named PDF in the node is absent. The item's source and statement are preserved; the proof is explicitly agent-written, assembled from local Stacks sources, rather than represented as a reading of that missing PDF.

## Findings and corrections

The imported item was unsplit, with no proof. Its statement is true as written, and no statement dispute is needed. Its warning about arbitrary base change is essential: global closure need not pull back to fibre closure. The proof uses an open etale atlas and an open projection under extension of fields for the two closure identities that it actually needs. Neither properness nor a group law enters this dimension argument.

I retained the item's existing search records and added only searches actually run through `msearch.py`. All new-node records copy the exact query text and actual full answers; the log records their execution. LeanFinder was tried with two phrasings for both the item and the new lemma. LeanSearch, Loogle, and source grep also ran. The hits concern Chevalley, constructibility, smoothness, Noetherianity, dominance, or general subspace dimension; none states either result for the objects here. The second generic grep in `AlgebraicGeometry` found no hits. There were no unavailable services in these searches.

An initial source-place label in the draft called the Noetherian-topology lemma 03II; reading the cited node corrected it to 04ZF. The proof's notation for the geometric inverse image was simplified to $E_{\bar t}$. The report and split do not introduce a replacement proof route at the unit or chapter levels.

## Not duplicates

lem-sfb-generic-residue-transcendence-dimension-bound vs lem-trf-closed-dominant-dimension: the existing node (02JX) assumes both schemes integral and the morphism dominant, and uses their function fields; the new 0BAG statement applies to arbitrary locally finite type sources and uses every irreducible-component generic residue extension, without dominance. The new node is not a specialization of that statement.

lem-sfb-generic-residue-transcendence-dimension-bound vs lem-trf-local-dimension-formula: the existing 02JU node assumes an integral dominant morphism and gives a local-ring inequality; the new result gives global dimension bounds for reducible, nondominant sources. It is not a clause of the item: it has no constructible locus, closure, smoothness, fibre avoidance, arithmetic-base, or complementary-open hypothesis or conclusion.

lem-sfb-generic-residue-transcendence-dimension-bound vs lem-zl-source-dimension-fibre-bound: the existing source theorem requires a dimension bound on every whole topological fibre. The new theorem requires bounds only on residue transcendence degrees at source component generic points. In this application the closure can have larger special fibres, so the existing theorem's hypothesis is not available.

No existing DAG node carries 0BAG or 0BAY. Whole-blueprint searches for `0BAG`, `generic dimension`, `closure dimension`, and `etale dimension` found no duplicate. The coordinate-generic-dimension node returned by `generic dimension` concerns a coordinate map in a closed affine embedding and shrinking a base, not this inequality. Whole-DAG tag and concept searches, together with the source-library search, preceded creation. The new node's nearest blueprint ancestor is null, as `tools/blueprint_refs.py ancestor` reports for this ancestry; its `from.place` and `via` preserve that ancestry and name the exact dimension-counting input. The item's `same_as` remains an explicit empty list.

## Review by Q96

I read the stage-1 brief, stage contract, worker role, GOAL, SETUP's three levels and the B--E return examples. I read the item's chapter and unit records, then the current blueprint's `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This work remains the auxiliary dimension count in the recorded alteration/Picard/finite-translate ancestry. The current blueprint's shorter compactification paragraph is not used to change that ancestry or to bypass any assigned unit step.

For the item I read `morphisms.tex` 0BAG and its input 0BAE, `topology.tex` 005K and its proof, `spaces-properties.tex` 03IQ, `decent-spaces.tex` 0A4J and the locally-quasi-finite dimension comparison, `spaces-morphisms.tex` 04NS, and `morphisms.tex` 0383. For the sole new node I read the exact 0BAG statement and proof and the 0BAE formula. Its proof is intentionally not put in the new node: for its future worker, 0BAE bounds each source local-ring dimension by the corresponding target local-ring dimension plus the maximum generic residue transcendence degree, minus a nonnegative residue transcendence degree. The generic bound makes this at most d+n; taking the supremum of local-ring dimensions (04MU) gives the assertion, including empty schemes. This explains the intended source without pretending to split the new node.

I opened and read the statement of every cited node. In particular, the open-map node gives openness and continuity of the etale atlas, the reduced-closed-support node gives support after *every* base change without asserting reducedness of that base change, the field-dimension node requires separated finite-type objects, and the generic dimension node requires only local finite type and a locally Noetherian target. These distinctions are used in the following step audit.

1. Negative n means every geometric inverse image is empty by the dimension definition. A point of Z gives a field-valued point; the algebraic-closure existence node and geometric-point definition place it in a geometric inverse image, contradicting emptiness. This is an elementary use of the cited definitions and field-existence statement. Nonempty T and c>D imply D is a finite nonnegative integer before the generic dimension theorem is applied.

2. The arithmetic Noetherianity node states exactly that finite-type integer schemes are Noetherian. The affine-atlas node requires only quasi-compactness of the point space, obtained explicitly from quasi-compactness of q and T. Chartwise composition gives a smooth, surjective, locally finite-type scheme map U to T. The local-Noetherianity node applies to that scheme map. The Noetherian-point-topology node applies to the affine, quasi-compact, locally Noetherian U. No assumption of a schematic X is made.

3. The two-line ascending-open argument proves the quasi-compactness of every open of U. Thus f is quasi-compact, and the definition node supplies finite type; the finite-type base-change node supplies finite-type fibres. Separatedness of those scheme fibres is proved by the displayed relative-diagonal pullback, using that U itself is affine. This verifies the finiteness and separation hypotheses needed in steps 7 and 9.

4. Constructibility is used only for the finite locally closed decomposition given in the constructible-subset node's statement. The point/open-calculus node supplies continuity and openness, which prove the exact identity H=p^{-1}(closure Z) by neighbourhoods. The scheme reduced-closed-structure node supplies H as a genuine scheme. Immersions are locally finite type by the cited statement, and chartwise composition makes H to T locally finite type. Nothing here identifies H_t with closure(E_t).

5. All base changes of p used here are surjective etale by the representable-etale scheme-test node. The reduced-closed-support node realizes closure(Z_bar) as B and its pullback as the closed scheme V. B is quasi-separated because it is a closed subspace of the separated geometric fibre. On every scheme chart, etale composition and the target-scheme etale/local-quasifinite statement give the precise local-quasifiniteness hypothesis of the scheme-source/algebraic-space-target dimension node; I do not apply that target-scheme lemma directly to a space target. The latter node states dim V <= dim B, exactly what is used. V is closed and contains E_bar, so contains its closure.

6. I wrote the chain proof of arbitrary subspace dimension monotonicity and homeomorphism invariance. This uses only the topological dimension definition: closures recover a chain upon intersection with the subspace, so no strict inclusion is lost. It justifies every later subspace comparison and is a proof step, not a new node or a citation to a definition for an unstated theorem.

7. The field-base-change projection is open by the universally-open-over-a-field statement; the step 4 neighbourhood proof therefore gives the needed closure identity for that projection. The reduced closed A_t is separated and finite type by step 3 and its closed immersion, so the *full* hypotheses of the separated finite-type field-extension dimension statement hold. The support theorem identifies its base-changed support without asserting that the base change is reduced. Thus the ordinary closure has dimension at most n. This is the correction to the tempting, unjustified arbitrary-base-change closure argument.

8. The finite-components statement applies to the closed subset H in the Noetherian scheme U. Scheme sobriety gives the generic points. Isolating each component and using the finite locally closed decomposition gives the explicit 005K argument putting every component generic point in E. There is no use of a definition as a substitute for the finite-components or sobriety theorem.

9. The finite-type-over-a-field point-closure statement applies to the nonempty irreducible closed closure of u_t in U_t, whose finite type was checked in step 3. It says exactly that its dimension equals the residue transcendence degree. The fibre-product-point residue-field statement supplies the fibre residue identification through the displayed tensor product, and the closed-immersion residue-field node supplies the other identification. Hence the new generic dimension theorem's hypothesis is proved for H itself, not only for U.

10. I checked all three hypotheses of 0BAG's numeric specialization: T locally Noetherian, H to T locally finite type, and every source component generic residue transcendence degree at most n. D+n<r is the literal c>D arithmetic. This is the only use of the new node.

11. The atlas-dimension node applies after geometric base change because q is quasi-separated and p_bar remains surjective etale. Pure nonempty geometric fibres have dimension r. Hypothetical containment gives full support of H_bar in U_bar by the closed-support statement, *not* equality with closure(E_bar). The separate source-library field-extension inequality applies to H_t because its map to the residue field is locally finite type by the base-change node. The ordinary fibre definition supplies the homeomorphism onto a subspace of H. These statements give r<=dim H_t<=dim H<r for arbitrary algebraically closed extensions and prove the contradiction.

12. The open-subspace definition supplies the scheme-chart open restrictions. The open-immersion/smooth-composition statement proves smoothness on those charts. Nonempty geometric fibres and the point-space image/base-change criterion give surjectivity. This includes the zero/empty-locus cases and does not require properness.

I tested the item on r=0, c>r, empty Z, a nonclosed open locus, reducible and nonreduced bases, and nonproper affine-space families. For r=0 or c>r, n<0 forces Z empty as step 1 says. Constructibility is indispensable: the generic point of Spec Z is dense but is not constructible, so a fake finite-stratification argument there would fail. For a genuine jump, over T=A^1 over a finite field, in X=A^3_T take Z defined by t*x=0, t*y=0, z=0, t!=0. It has dimension-zero nonempty fibres away from t=0 and empty fibre there; its closure is x=y=z=0, not the apparent unclosed equations at t=0, and misses every full fibre, consistently with D=1, r=3, c=3. To exhibit the need to distinguish fibre closure, use instead x*t=1, y=z=0 over t!=0: the closure has empty special fibre, also consistent; neither example licenses a general base-change closure identity. More sharply, Z={y=0,t!=0} in A^2_T has closure {y=0} and empty Z_0 but nonempty closure fibre, demonstrating the invalid identity while still avoiding a whole fibre. The c>D hypothesis is not satisfied by this last codimension-one example when D=1; it is a check of the forbidden inference, not a counterexample to the item.

For the new lemma I tested a point/affine line over a field (d=0, n=0/1), closed immersions (generic n=0), disjoint components of different dimensions, nondominant maps, and empty sources and bases. The numeric inequality is one-sided, so it asserts no unwarranted equality for open maps. It does not require equidimensionality or catenarity. There is no new definition, no new node repeating an item clause, and no hidden proof in the new statement. Each proof step is below 2,000 characters. The dependency audit found no path back to the item. Every off-unit statement is declared in split_report.tool_uses as a generic chart, field, or dimension tool; no unit route is replaced. No SGA source is used.

## Unfinished work

The new 0BAG prerequisite remains statement-only by the one-level splitting rule. No item proof step is left unfinished. Server dry-run and push results are recorded by the delivery tool; a passing dry run is required before the push.
