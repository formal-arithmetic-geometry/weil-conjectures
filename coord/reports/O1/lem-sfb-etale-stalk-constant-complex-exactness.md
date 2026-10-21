# Stage-1 report: lem-sfb-etale-stalk-constant-complex-exactness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-constant-complex-exactness.json`: statement, now split in six steps; not a Mathlib leaf as a whole. Statement and statement dependencies retained exactly. No new nodes; no new Mathlib leaves.
- `citations.json`: six entries, one per step/node citation, with verbatim statement excerpts.
- `report.md`: this report. Search records remain in `searches.jsonl`; `write_split.py` is sandbox-only preparation code.

## Attachments

None for this item. I searched `lean/WeilConjectures/` for the exact blueprint id and for constant/stalk, sheafFiber/constantSheaf and homology terminology. No project declaration states every clause of the item. `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso` and `constantSheafCompSheafFiberIso`, in `lean/WeilConjectures/Mathlib/CategoryTheory/Sites/Point/ConstantSheaf.lean` (lines 85 and 117), supply the constant-fibre part, not the complete theorem on both exact termwise functors and unbounded cohomology. I read that file, including the naturality and germ normalization. These partial results do not justify ATTACH.

## WANTED

None. All needed sources are present locally.

## What was wrong or changed

The imported item had a complete intended statement but no proof. I supplied the proof without changing any hypothesis, conclusion, coefficient category, or blueprint route. The general constant-germ and exact-functor results are already nodes, so no new node is needed. In particular I did not cite `lem-constructible-constant-exact`, which assumes both a finite ring and finite modules, for the assertion about arbitrary modules. I did not cite `lem-weil-pbc-module-stalk-exact`, which concerns ordinary stalks on ringed spaces, for an etale geometric stalk.

The literal statement has one grammatical ambiguity: “Both” after introducing C and E refers to S and c, as confirmed by the next sentence and source. No mathematical repair is needed. The second cohomology comparison is an isomorphism of A_T-module sheaves (and hence A-linear through constant scalars); it is not an isomorphism to an ordinary A-module.

## Proof and searches

1. Apply exact module-presheaf sheafification to a sectionwise short exact sequence of constant module presheaves, over the constant presheaf of rings A. Its sheafified ring is A_T. This proves exactness of c for all modules.
2. Use the existing normalized constant-abelian-stalk isomorphism and explicitly verify multiplication, scalar compatibility and naturality on germs. This identifies the stalk ring with A and gives the ordinary module action and the natural eta_M.
3. Forget a short exact sequence of module sheaves, use exact abelian geometric stalks, and observe that kernels/images/surjectivity of linear maps do not change on forgetting ordinary module scalars. This proves exactness of S.
4. Apply the existing Mathlib-leaf cohomology comparison to both functors.
5. Write out the consequences for zero cohomology and maps inducing cohomology isomorphisms.
6. Apply eta_M degreewise and check the differential, inverse-chain-map and complex-map naturality equations.

The item's inherited Mathlib searches were preserved. I ran six additional searches through the required msearch command: LeanFinder with two distinct phrasings, Loogle for sheafFiber and constantSheaf, LeanSearch for the entire theorem, and two grep patterns. All services answered successfully. I read their hits. The Zariski module tilde/stalk and condensed locally constant module hits concern different objects. `PresheafOfModules.sheafificationCompToSheaf` is a compatibility of module sheafification and forgetting, not the whole assertion. I read Mathlib `CategoryTheory/Sites/Point/Skyscraper.lean` around lines 270–298 (`presheafToSheafCompSheafFiberIso`) and `Algebra/Homology/ShortComplex/PreservesHomology.lean` lines 45–65 and 770–785 (`preservesHomologyOfExact`, `homologyFunctorIso`). These are ingredients, already represented by existing DAG nodes; they do not directly state this item's complete normalized module-complex result.

Before deciding against new nodes I searched the whole DAG by tags 03EI, 04EQ, 03PT and exact/stalk/constant/cohomology terminology, and the blueprint with `blueprint_refs.py search` for etale stalk constant complex exactness, stalk exact, constant sheaf, exact functor, and constant-complex. The nearest ancestor is `det-ctf-finite-proper-tor`. I read its current main-20261015 proof, especially the “From constant modules to all sheaves” paragraph, and the chapter and unit records. The present argument supplies precisely the exactness and constant-acyclic-complex test needed by the parent K-flat argument; it introduces no different six-functor route. This item is not the unit's key node, so no unit realization record was changed.

## Not duplicates

No new nodes. Existing nodes are reused: `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`, `lem-weil-pbc-constant-sheaf-geometric-stalk`, `lem-weil-pbc-module-sheaves-colimits-forgetful`, `prop-weil-pbc-geometric-stalks-exact`, and `lem-weil-pbc-exact-functor-complex-cohomology`. The latter and the exact sheafification/abelian stalk nodes are Mathlib leaves. The normalized ringed-site exactness lemma is also present, but would require introducing its normalized-point presentation; the proof here instead uses the already available faithful exact forgetful statement and exact abelian stalks directly.

## Review by O1

I read the required delivery-errors sections B–E in full, including their mirrored versions. For the item's source I read Stacks `sites-modules.tex` Tag 03EI (`lemma-sheafification-exact`), Tag 04EQ (`lemma-stalk-exact-modules`, including all three clauses and its preceding germ-action construction), Tags 03DA/03DB (`lemma-abelian`, `lemma-limits-colimits`); `etale-cohomology.tex` Tag 03PT (`lemma-stalk-exact`, including the sheafification/germ map); and `homology.tex` Tag 010N (`lemma-exact-functor` and its kernel/cokernel argument). I checked all five tags against `stacks-project/tags/tags`. No SGA source is used and no literature is missing. There are no new-node sources to review.

For step 1 I opened the full statement of the cited sheafification node: its clause (1) supplies sectionwise exactness of module presheaves and its clause (2) exactness of sheafification. Its source explicitly specializes the constant presheaf of rings, so the output acts over A_T, not over an incorrectly substituted section ring A_T(U). The elementary constant-presheaf part is written in the step itself. Arbitrary A and arbitrary modules satisfy its hypotheses.

For step 2 I opened the full statements of the constant-sheaf-geometric-stalk node and the geometric-stalk definition. The former explicitly gives the map at the identity neighbourhood (T,t), not merely an unspecified abstract isomorphism. It only claims an abelian isomorphism, so the proof does not silently take module linearity or ring structure from it: it derives the identities eta_A(ab)=eta_A(a)eta_A(b) and eta_M(am)=eta_A(a)eta_M(m) by the defined germ operations and writes naturality for each module map. Thus the extra scalar claim is a direct operation calculation, not a missing cited theorem.

For step 3 I opened the statement of the module-sheaves-colimits-forgetful node. Its clause (1) says the forgetful functor is faithful and exact, preserving kernels and cokernels, for any sheaf of rings on a site with abelian sheafification, explicitly including the small etale site. I also opened the statement of the exact-geometric-stalks node, which applies to all abelian etale sheaves without finiteness restrictions. These statements give exactly the two non-elementary facts used. Reflection for ordinary modules is verified explicitly by equality of the subgroup and submodule kernels/images; no ringed-space stalk lemma is substituted for an etale statement. Additivity is already checked on germs.

For step 4 I opened the entire cohomology-comparison statement: it is for integer-indexed cochain complexes with no boundedness assumption, is natural in complex maps, and identifies cycles and images compatibly with their maps. This is precisely what the step uses, after steps 1 and 3 verify its exact additive hypotheses. It is an isomorphism in each target abelian module category, giving the required linearity. Step 5 only uses that comparison, its naturality, and the definitions of zero cohomology/quasi-isomorphisms; it displays the conjugation formula, rather than hiding a localization theorem. Step 6 uses the explicit naturality from step 2 with the differentials and each component of a complex map. I checked the direction E -> S(cE), the chain equation, and that multiplying it by the inverse components gives an inverse chain map. These last two steps add no uncited non-elementary fact. Every cited node/step pair has a verbatim excerpt in citations.json; I checked the excerpts against the actual statements.

The generic constant-stalk normalization and module-sheaf forgetful exactness are declared as off-unit tool uses in split_report.tool_uses. They do not replace the unit's route: they are prerequisites for its stalkwise Tor-amplitude argument. I have not written top-level tool_uses or changed another node.

I tested the edge cases A=0 (all modules and operations are zero), nonreduced A=Z/4Z (no use of field or flatness assumptions), T disconnected (constant germs still take the specified value on each component), and the empty scheme (no geometric point exists, so the stalk assertion has no instance). For complexes I checked a module in a single negative degree, A -> A with identity differential, and the two-sided unbounded exact complex with every term A^2 and d(a,b)=(b,0): d^2=0 and both kernel and image are A x {0}. The proof applies in every degree and introduces no truncation, infinite totalization or convergence step. I also checked eta on multiplication by a nonunit in Z/4Z, so its claimed linearity does not rely on invertible scalars. No step exceeds 2000 characters, and no comparison lemma is hidden in a long step. No false or ill-typed statement was found, and no STATEMENT-DISPUTED correction was needed.

## What remains unfinished

No mathematical part of the assigned one-level split remains. Server dry run and direct push are performed after this report; their result is the final delivery response. No Lean was written, no compiler/Lake/build was run, and all writes are confined to the assigned sandbox.

The first captured dry run rejected the short formula-only excerpt for the geometric-stalk definition. I replaced it with the entire verbatim definition, including the pointed-neighbourhood indexing convention; the proof did not change.
