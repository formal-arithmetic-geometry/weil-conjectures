# Worker report — Q117

## Files written

- `dag/nodes/sec-six-functors/lem-sf-forgetful-representing-pair-right-mate.json`: item, statement, split into six explicit steps. The statement and its statement dependency are unchanged. Mathlib verdict: no complete match.
- `citations.json`: one verbatim statement quotation for each of the two step/node citations.
- `searches.jsonl`: actual results logged by the prescribed msearch command; the item retains its inherited searches and appends the five searches from this session.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files or unit/chapter records were written, and no compiler or build tool was run.

## Attachments

None. Searches for the blueprint tag, representing pairs/lifts, universal arrows, forgetting and right mates under `lean/WeilConjectures/` found no declaration giving all clauses. I read `CategoryTheory/Adjunction/UniversalArrowMate.lean`: its `bijective_comp_map_of_unit_comp_map` assumes an invertible mate and transports universal arrows in the other direction; it does not prove this criterion. The other right-mate hits concern particular open pullback squares or compatibility of derived squares, not arbitrary forgetting.

## WANTED

None. The proof is an agent-written elementary expansion of the supplied blueprint provenance, with the existing mate-bijection node as its only external mathematical tool.

## Findings and corrections

The imported item had an empty proof, not an incorrect statement. Its mathematical statement remains verbatim. I constructed the inverse representing map directly instead of assuming that an arbitrary forgetful functor reflects or detects isomorphisms. I derived the unit equation from the inverse mate formula, so it is an identity for the two specified adjunctions, rather than an unspecified adjunction transported along an isomorphism.

I read the current blueprint file `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`, particularly its last sentence about the same units and counits giving the exceptional-adjunction assertion. It does not itself contain numbered Steps 7–8: those words in the existing source describe the parent split's old proof. I preserved that provenance and marked my proof as agent-written. I also read the item's chapter and unit records. This is a general categorical calculation below the unit, with no alteration of its geometric route. The inherited provenance has no imported ancestor: the prescribed ancestor command reports `blueprint.from.node = None`. Its explicit place and via chain are retained; no invented blueprint ancestor is substituted.

## Mathlib and blueprint searches

I read all five logged results from this session: LeanSearch for the full criterion; Loogle for `"rightAdjointUniq"`; grep for `mateEquiv_counit|rightAdjointUniq|rightAdjoint.*mate` in `CategoryTheory/Adjunction`; and LeanFinder for both the full criterion and a second phrasing using objectwise universal arrows without fullness/faithfulness. All services answered successfully.

I read `Mathlib/CategoryTheory/Adjunction/Unique.lean:102–142`, `Mates.lean:84–155`, and the relevant documentation and constructions in `Lifting/Right.lean:10–43,112–192`. Uniqueness compares two already specified right-adjoint functors, while here the representing objects are only objectwise data. The lifting theorems use regular-mono/comonadic and equalizer hypotheses absent from the item. The mate formulas match the existing `def-weil-pbc-adjunction-mate` leaf, which is reused. None of these is a one-line proof of the whole criterion: one must still construct the unique representing isomorphism and compute the underlying mate.

Before deciding that no helper node was needed, I searched the whole DAG by representing-pair, uniqueness, adjunction and mate terminology, and searched the whole imported blueprint with `blueprint_refs.py search` for representing, representing pair, right adjoint and mate. I opened the statements of `det-sp-representing-pair-uniqueness`, `lem-pur-fixed-pair-right-adjoint-comparison`, `lem-sfb-coherent-right-adjoint-comparisons`, and `lem-sbc-reflector-square-mate-factorization`. The first has a special geometric setting, the second works with fixed-pair categories and a prescribed carrier, the third compares adjoints on the same categories, and the fourth compares reflector squares without claiming invertibility. None states the full arbitrary-forgetting criterion. No new node was created for an elementary specialization or a clause of the item.

## Not duplicates

No new nodes. The existing mate-bijection leaf is reused directly.

## Review by Q117

I checked the split against sections B–E of `coord/delivery-errors.md` with the item, its source and the mate node open. The only outside result is the statement of `def-weil-pbc-adjunction-mate`, which I read in full: it gives the natural transformation with the specified transpose and the inverse transformation formula. I also read Stacks Tag 07A7, label `remark-base-change`, in `literature/stacks-project/sites-cohomology.tex:4033`: it supplies the counit-transpose convention, not the full arbitrary-forgetting theorem. No new source-only assertion is used as a lemma.

Step 1 uses exactly the two Hom bijections assumed in the item. Choosing preimages of the two counits and applying injectivity to the two composites constructs both inverses; the uniqueness claim follows from the same injectivity. This is a few-line argument from the hypotheses, so I kept it as an elementary step, not a separate uniqueness lemma.

Step 2 uses the cited mate node with the native adjunction first, the ordinary adjunction second, horizontal functors U_X and U_Y, and alpha = c inverse. All four functors and both adjunctions have precisely the directions required by that statement. The copied quote gives the transpose used here. The resulting natural transformation uses no representing choices.

Step 3 uses naturality of c at the actual native morphism h, the assumed equation for U_Y(d), and Step 1's counit equation. I checked every intermediate map: its source is F(U_X(G^W L)) and target is U_Y L. Ordinary adjunction injectivity then identifies the mate, without testing equality using either forgetful functor. Step 4 explicitly constructs both inverse composites and derives naturality of the inverse by multiplication from the known naturality of beta. This needs no functorial choice of H_L.

Step 5 is explicitly non-elementary and again cites the mate node, now its inverse formula, whose quotation is recorded verbatim. Evaluation at K has source F(U_X K) and target U_Y(F^W K); the right side is c_K inverse with exactly that type. Applying the inverse ordinary transpose map produces beta at F^W K composed with U_X(eta^W_K). Finally G(c_K) cancels G(c_K inverse). Thus both asserted identities use the specified units and counits and the correct orientation of c.

Step 6 repeats the already established factorization for an arbitrary second triple; its canonical comparison is h'_L h_L inverse, and the second triple's stated representing bijection gives uniqueness. Its underlying equation follows by right composition with U_X(h_L inverse). No general Yoneda theorem, uniqueness-of-adjoints theorem, or reflection-of-isomorphisms assertion is hidden here. Every non-elementary operation is precisely the cited mate-bijection statement; the other steps are the written substitutions in given bijections. Every step is shorter than 2000 characters, and the proof dependencies are exactly the union of the uses.

I tested the orientations on the one-object category of the cyclic group C3 with all functors identity, both adjunctions identity, c a nonidentity central group element z, e = 1 and d = z. The representing bijection is multiplication by z, so h = beta = z inverse; both the unit and counit equations become z times z inverse = 1. This detects accidentally replacing c inverse by c. To check the absence of faithfulness/fullness assumptions, take a groupoid with two disconnected objects, each with automorphism group C2, and collapse it to the terminal category for both U's. That functor is neither faithful on automorphisms nor full between the two objects. With both adjunctions identity, H_L = L and d_L identity satisfy the hypotheses, and the asserted beta is the identity of the terminal category. Empty categories give vacuous component assertions whenever the stated functors/adjunctions exist. No extra smallness, colimits, or functorial representing choices enter the proof.

## Unfinished work

None in the mathematical split. Final remote validation and direct delivery follow the repair below.


## Repair of the side-completion landing refusal

The returned delivery was approved mathematically but was not merged because its completion existed only in the side DAG. I continued the retained sandbox associated with the earlier dry-run receipt at `5a9a0f8a2ab`, retaining all six proof steps, citations and logged Mathlib searches. I compared the retained node with the current read clone: the current live item is unsplit with an empty proof, and its statement, statement dependency, source, blueprint provenance, creation record, chapter and unit agree exactly with the retained item. The differing fields are precisely the split's proof, proof dependencies, proof origin, searches, status and split report. There is no released repair note for this item in the read clone.

The required initial dry run rebuilt the delivery on the current server DAG and exited successfully at `f0d81b52992`; this confirms that the side completion has not superseded this live unsplit item. The delivery tool resolves current `origin/sheaf-dag` itself, overlays the split-owned fields, and retains current maintainer metadata. This repair likewise starts its sandbox node from the current live node and overlays the retained split fields, rather than restoring the old delivery branch.

I reread the entire current `def-weil-pbc-adjunction-mate` statement, its Mathlib match and status, and both quotations in `citations.json`. Both quoted formulas remain verbatim parts of the current statement: Step 2 takes its counit-transpose construction, and Step 5 takes its inverse bijection formula. The category and functor assignments in Step 2 still match all its hypotheses; the unit calculation in Step 5 still has source `F(U_X K)` and target `U_Y(F^W K)`. I also reread Mathlib's `mateEquiv`, its inverse and unit/counit equations in `Mates.lean:84–155`. No mathematical citation replacement is required. I corrected Step 5's classification to non-elementary because it invokes that inverse mate theorem, retaining its explicit node citation and quote. This is a proof-record correction in addition to the rebase, not an unchanged re-push.

I reread the current blueprint final exceptional-adjunction sentence and Stacks Tag 07A7's counit-transpose construction; neither is used to infer any fullness or faithfulness. Steps 1, 3, 4 and 6 remain the explicit injectivity, naturality and cancellation arguments reviewed above, and all steps remain below 2000 characters. The recorded C3 orientation test and disconnected C2-groupoid test still apply to the unchanged statement. The current project source search again found no exact attachment. I read the retained search log rather than rerunning unchanged search questions. No new node, source, statement alteration, Lean file or build was introduced by this repair.
