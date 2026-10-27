# Stage-1 report: lem-sfb-space-proper-support-universal-purity

Group Q51, direct delivery, 2026-10-24.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-universal-purity.json`: statement, now split into six proof steps. Mathlib verdict: no matching theorem; original searches retained and five actually executed Q51 searches appended.
- `citations.json`: 15 entries, one per cited node per proof step, with verbatim substrings checked against the live node statements.
- `report.md`: this report.
- `searches.jsonl`: produced by the required msearch.py command; its results were read.

There are **0 new nodes and 0 new Mathlib leaves**. Existing nodes already supply all the non-elementary inputs, so no replacement theorem or clause of the item was introduced as a child.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id and for proper support, impurities, relative purity and universal purity. The universal-purity hits concern weights of polynomials and the proper-support hits concern other scheme theorems. No project declaration states this algebraic-space relative-purity theorem. No Lean was written and no compiler, Lake or build tool was run.

## Wanted literature

None. All mathematical sources used are present under `literature/stacks-project/`.

## Findings and corrections

The item statement is correct in its given carrier convention: the proper map of the closed carrier to Y is its composite with f, as in the referenced proper-support definition. Its statement and statement dependencies are unchanged. The original item had no proof; it now has the complete support-and-closed-image argument underlying Stacks 0CVI(1).

The latest blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), compactification/direct-image preservation. The inherited chain reaches this module-theoretic input through the stable-moduli/Quot/flattening prerequisites. This input does not replace the unit route. The local unit JSON still points to the older sec-six-functors unit with the same id; the current latest blueprint puts the relevant unit under sec-six-functors-basics. Neither unit record was changed. The inherited `blueprint.from.node` is null and `blueprint_refs.py ancestor` returned None; the existing detailed place and via chain were preserved. Searches of the whole imported blueprint for `proper support` and `relative purity` found no theorem stating this item. The former returned cohomology/compact-support results, and the latter returned no nodes.

A tempting shortcut would claim the module descends to the reduced support. That is false, for example for the structure module on a nonreduced closed subscheme. The proof instead uses the reduced support only as a proper space with the correct underlying closed point set; no module is placed on that reduction. It also does not apply the existing flat/finitely-presented proper-support base-change theorem: the item assumes neither relative flatness nor finite presentation of the module. The finite-type support-pullback theorem has exactly the weaker hypotheses needed here.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The DAG was searched for Stacks 0CVI, 0CZI, supported-on-closed, support/pullback, closed pushforward, and proper base change. Existing support, stalk, closed-subspace and base-change nodes are cited directly. In particular the existing proper-carrier/scheme-theoretic-support equivalence was read but is not needed; its conclusion alone would not justify identifying the reduced support with a module carrier.

## Review by Q51

I read the item source in spaces-flat.tex, Tag 0CVI (lemma-proper-pure), including its reduction through the closed carrier and its final universally-closed-image argument. I also read spaces-perfect.tex Tag 0CZI (lemma-module-support-proper-over-base), especially (3), to check that the item has the same proper-support hypothesis. My expansion keeps that argument but realizes the reduction with topological supports and existing DAG inputs, rather than creating a new closed-immersion purity-invariance theorem. No SGA source is used.

For step 1, I opened the statements of lem-sfb-space-finite-type-support-pullback, lem-sfb-space-closed-pushforward-geometric-stalks, lem-sfb-space-closed-subspace-proper and def-sfb-space-morphism-properties. The first explicitly says a finite-type quasi-coherent module has closed support; the second explicitly gives zero geometric stalks off the closed subspace, also for the underlying abelian sheaf of N. The third says a closed immersion is proper, and the definition says proper includes universal closedness. Thus the point image A of Z is closed by applying that definition to the identity base change. These are precisely the facts needed to prove T = Supp(M) is a closed subset of A. I read their source passages in spaces-morphisms.tex Tags 07TZ (lemma-support-finite-type), 04E5 (lemma-closed-immersion-push-pull), 0DK1 (lemma-stalk-push-closed) and 04XZ (lemma-closed-immersion-proper). The 0DK1 formula has swapped stalk labels in the TeX; the existing node already records the correctly typed formula. This proof needs only the complement-vanishing clause, explicitly given by 04E5(2), so it does not use that misprinted formula.

For step 2, I opened lem-sfb-space-proper-support-closed-operations and lem-sfb-space-reduced-closed-support. The former states both the equivalence between existence of a proper closed subspace with a given point set and properness of the reduced induced subspace, and inheritance by closed subsets. Its local-finite-type hypothesis holds because f is finite type. Apply the equivalence first to the given carrier with point set A, the subset assertion to T, and the equivalence again to the reduced induced W on T. The latter node gives existence of W. I read spaces-perfect.tex Tags 0CZC (lemma-closed-proper-over-base) and 0CZE (lemma-closed-closed-proper-over-base), and spaces-properties.tex Tag 03IQ (lemma-reduced-closed-subspace). This is a use of the stated theorems, not their proofs. It neither changes the scheme-theoretic carrier nor asserts that its nilpotents annihilate M.

For step 3, I opened lem-sfb-space-proper-base-change, lem-sfb-space-reduced-closed-support and lem-sfb-space-finite-type-support-pullback. They explicitly provide, respectively, properness of W_B over B without finiteness/flatness conditions on B to Y; the closed immersion and homeomorphism onto the inverse image of the closed support T; and finite-type quasi-coherence of M_B together with the exact inverse-image formula for support. The fibre-product identification W times_Y B = W times_X X_B is its universal property. I checked their source statements in spaces-morphisms.tex Tags 04WP (lemma-base-change-proper) and 07TZ(3), and spaces-properties.tex Tag 03IQ with Tag 03H4 (lemma-points-cartesian) as used by the existing reduced-support node. B can be any scheme, and W_B need not be reduced.

For step 4, I opened def-sfb-space-universal-relative-purity, def-trf-relative-assassin and lem-sfb-space-etale-chart-support. The first actually defines the space relative assassin by images of relative associated points on etale scheme charts. The second actually defines associated points by element-annihilators on stalks and the relative assassin by the fibre modules. Thus the witnessing fibre stalk contains a nonzero element. A zero original module stalk would give a zero fibre stalk by tensoring zero, contradicting that witness. The third node explicitly equates chart support with the inverse image of geometric-stalk support on the space, so it places xi in Supp(M_B). I read spaces-flat.tex Tags 0CV8 (definition-impurity) and 0CVD (definition-pure), divisors.tex Tag 05AT (definition-relative-assassin), and spaces-morphisms.tex Tag 07TY (lemma-support-covering). This step is elementary from those cited definitions and equality; it uses no associated-prime base-change theorem or hidden flatness claim.

For step 5, the cited definition of properness gives that the point map of the already-proved-proper h:W_B to B is closed. I use the homeomorphic closed-subspace identification explicitly stated by lem-sfb-space-reduced-closed-support. The set C is the closure of the chosen point w, its closed image contains b-prime, and every closed set containing b-prime contains its specialization b. Choose v in that image fibre. Closure in a closed subspace is ambient closure, so its image theta specializes from xi in X_B. This is the elementary topological argument written in full, exactly as in the final paragraph of 0CVI. It neither assumes the underlying topological fibre product equals a fibre product of point sets nor claims factorization of a morphism from mere containment of point images.

For step 6, def-sfb-space-universal-relative-purity explicitly requires such a theta for every proposed impurity and every scheme base change. Step 5 supplies it. There is no restriction on b, b-prime, or B, so this is the full universal conclusion of the item.

I checked B--E of delivery-errors.md against these files: every non-elementary input is an existing cited statement, each quotation is verbatim, no new node needs a missing definition or a search, and no proof step is a reference standing in place of an argument. All six steps have fewer than 2000 characters. The statement and notion categories agree with the source (finite-type quasi-coherent modules on small etale ringed sites, not constructible coefficient sheaves). There is no unsupported appeal to a theorem under extra hypotheses.

Small cases checked: M=0 and empty X or empty Z give empty support and no associated-point witnesses, so purity is vacuous. Identity base change gives the same closed-image proof. Non-flat B to Y is allowed by both cited base-change results. A nonreduced carrier still has the same support point set; W_B can acquire nilpotents and nothing requires it to remain reduced. Modules need not be flat or finitely presented. The morphism X to Y need not be proper; only W to Y is used as proper. No target statement, unit route or chapter record was changed.

## Remaining work

No mathematical gap remains in this one-level split. All proof dependencies already exist. Required server dry run and direct push are the final delivery operations; their result will be given in the terminal delivery answer.

The first delivery dry run requested a longer quotation for step 1: the correct literal sentence "Then i is proper" was below its 40-character minimum. I replaced it with the verbatim hypotheses and conclusion of the same cited theorem; no mathematical step changed. The separate server review_split check passed.
