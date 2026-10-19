# Stage-1 report: det-pe-replete-on-contractible

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-replete-on-contractible.json`: statement, split; full item has no exact Mathlib match. Four proof steps, no new nodes, no Mathlib leaves.
- `citations.json`: exact statement quotations for every step/node citation.

The statement is unchanged. The report and search log are in this sandbox. No Lean, chapter, unit, live repository, or launcher file was edited. This is the first worker's handoff; delivery is reserved for the second reader.

## Attachments

None. Searches of the read-only `WeilConjectures/` source for the blueprint tag, repleteness, weakly contractible objects, inverse sequences, and sequential limits found no project declaration stating both conclusions of this item. The ring-level w-contractibility results and the homotopy-limit commentary do not state it. The master checkout is reference material, not evidence of a finished proof.

## WANTED

None: the current blueprint statement and its separate `.proof.md` file contain the complete argument used here.

## What was wrong or incomplete

The imported mathematical argument is sound. Its statement dependencies were empty, its proof was one unsourced paragraph, and its `blueprint.same_as` had not been searched. I added the pro-etale site, weak-contractibility equivalences, and inverse-sequence/limit definition as statement dependencies, and expanded the proof into four sourced steps. The original statement and all imported metadata are preserved.

During my self-review I removed a provisional step that quoted the Mathlib zeroth-projection theorem directly without a corresponding DAG node. The final proof instead writes the two-line preimage-choice and recursion argument explicitly, then checks the lower indices separately. Thus there is no unrecorded non-elementary theorem hidden in step 2, and no unnecessary new node. The actual Mathlib queries, including the invalid Loogle query with unknown identifier `Pi`, are recorded honestly from `searches.jsonl`; an invalid query supplies no evidence of absence. The second semantic phrasing searches the full pro-etale statement rather than only its set-theoretic ingredient.

## What could not be finished

No mathematical gap remains. The required delivery dry run is run after the checks below; this sandbox will be left in its accepted state for the second reader, without pushing.

## Not duplicates

No new nodes were created. Whole-DAG searches and `tools/blueprint_refs.py search` for `replete`, `inverse sequence`, and `weakly contractible` found no other node stating both conclusions. In particular, `det-pe-replete-epimorphism` states a sheaf epimorphism, whereas the present item proves surjectivity of sections on a weakly contractible object and is used to prove that later statement. The finite-set inverse-limit leaf `lem-galois-inverse-limit-surjective` assumes finite nonempty sets, so cannot supply the unrestricted section sets here. The module-tower exactness node concerns modules, not arbitrary set sheaves. Existing weak-contractibility and inverse-limit nodes already give precisely the two non-set-theoretic inputs needed.

## Review by Q124

I read `coord/delivery-errors.md` B–E in full, the three blueprint levels in SETUP, this chapter and unit, the current statement, and the complete source proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-replete/det-pe-replete-on-contractible.proof.md`. The item realizes exactly step 1 of `sk-prop-pe-replete`: evaluate on a weakly contractible object, lift successively, determine earlier stages, and use sectionwise limits. It is not the unit's key statement, so I did not edit its realization fields. The hypothesis is an arbitrary weakly contractible object, with no affine, quasi-compactness, finiteness, or nonemptiness assumption added. The sheaves remain set-valued and the tower has precisely the specified epimorphic successor maps. No SGA source is used.

For step 1 I opened the current DAG statement of `det-pe-weak-contractible-equivalences`. Its clause 3 says verbatim that every epimorphism of sheaves induces a surjection on sections at W. Each given transition has exactly that hypothesis. The step uses this statement, not its proof, and `citations.json` copies clause 3 including its TeX delimiters.

Step 2 is elementary foundational choice and natural-number recursion: surjectivity gives a nonempty fibre for each pair (n,z), classical choice selects one preimage, and b_0=a, b_(r+1)=s_(m+r)(b_r) is a well-typed recursive definition. The right-inverse equation immediately gives the required adjacent compatibility. Nothing is inferred from the proof of another DAG node and no compatible sheaf-level choice is claimed. Step 3 is the finite descending definition of the earlier coordinates; checking n<m and n=m+r covers every natural number, including the junction at m. These are explicit equations rather than a black-box inverse-limit theorem, so they need no new node under the elementary-step rule.

For step 4 I opened the current statement of `det-pe-replete-definition`. It explicitly supplies both the sectionwise set of compatible tuples and the formula for each projection. Substituting V=W and the tuple from steps 2–3 gives a preimage of the prescribed a. The quote in `citations.json` includes the whole displayed formula and projection description; the brief phrase “Its limit is the sheaf” alone would have been insufficient. No theorem is taken solely from that definition node's proof.

I read the related pinned Mathlib declaration in `CategoryTheory/Limits/Types/Images.lean:80–121` (the theorem is at line 111) and its concrete-category variant in `CategoryTheory/Limits/ConcreteCategory/Basic.lean:93–104`. They provide a zeroth projection for an already-surjective set/concrete tower. They do not directly state both clauses on an arbitrary pro-etale weakly contractible object and arbitrary stage m. The generic projectivity and coherent-topology search hits are related ingredients, not exact matches for this item. Recording their existence does not justify extracting an elementary clause into a new node.

I checked m=0, m=1, and an arbitrary m: the tail starts at the prescribed value, the backward part is finite, and every compatibility equation holds. If F_m(W) is empty, projection surjectivity has no element to lift, so the proof never assumes nonemptiness. Empty fibres are never chosen: choices are indexed only by actual z in the target of a surjective transition. Constant towers, singleton section sets, and W empty are also covered. No compatibility with restriction maps or simultaneous choice over all W is needed, since the conclusion concerns the section map at one fixed W. Finally I verified unchanged statement text, exact citation substrings, equality of proof_deps with the step-use union, preservation of imported fields, and that no new-node B1–B8 or D1–D2 issue arises.


## Second reading by Q124

- Item statement: checked word for word against current blueprint `sec-proetale-coefficients/sk-prop-pe-replete/det-pe-replete-on-contractible.md`, and against step 1 of the unit and the complete separate `.proof.md`; PASS. Arbitrary scheme/site object, set-valued sheaves, epimorphic successor maps, weak contractibility, transition surjectivity and every natural-number projection are preserved. Its source names the blueprint, not a Stacks tag; no Stacks theorem or SGA reference is being imported by this split.
- Step 1: opened `det-pe-weak-contractible-equivalences`; condition 3 is exactly surjectivity on sections for every sheaf epimorphism at the given weakly contractible W. Each t_n has those hypotheses; PASS, using the statement only. The citation quote is verbatim.
- Step 2: checked against the blueprint's recursive lifting sentence and the surjectivity established in step 1; PASS, elementary. For each actual pair (n,z), its fibre is nonempty; choice supplies s_n(z), and recursion gives b_r in F_(m+r)(W) with t_(m+r)(b_(r+1))=b_r. Empty target sets require no choice of an element. This is foundational choice plus recursion, not a sheaf-level splitting theorem.
- Step 3: checked against the blueprint's descending earlier stages; PASS, elementary. The finite backward definition covers n<m, the recursive equation covers n>=m, and the junction at m uses b_0=a. At m=0 the backward part is empty; at m=1 its only equation is x_0=t_0(a).
- Step 4: opened `det-pe-replete-definition` and its blueprint source; its displayed compatible-tuples formula and coordinate projections state precisely the sectionwise identification used. PASS, elementary substitution of the constructed tuple, with no use of that node's proof. The full formula and projection description in citations.json are verbatim.
- New nodes: none; B1–B8 and D1–D2 introduce no new-node obligations. Independent whole-blueprint searches for `replete`, `inverse sequence`, and `weakly contractible` found the item and related definitions/module statements, but no duplicate giving both conclusions. `det-pe-replete-epimorphism` is the later local-surjectivity assertion and uses this item, so it must not be cited backwards.
- Mathlib/source attachment check: ran fresh LeanFinder, Loogle and Mathlib grep queries in different vocabulary via msearch.py; actual results are retained in searches.jsonl and appended to the item's mathlib_searches. Read `Types/Images.lean:80–121`, `ConcreteCategory/Basic.lean:93–104`, and `Sites/Coherent/SequentialLimit.lean:70–120`. These give set/concrete zeroth-projection or coherent-site local-surjectivity results, not the complete item. Read-only searches of slopmaster2 WeilConjectures and Comparator found only commentary on replete topoi, not an attachment for the item. No new Mathlib leaf is warranted.
- Edge cases and dependencies: constant singleton and empty-set towers, an empty target F_m(W), the empty scheme/object, and m=0,1 all satisfy the argument; no finiteness, affine, connectedness or nonempty-section hypothesis is used. Ring/field/zero-module specializations add no hypotheses since the statement is about arbitrary sets. The proof-dependency union equals the two cited nodes, and their statements supply all non-elementary facts. Every new statement is absent, so no small-case exception is left unchecked for a new node.

Changes made: added this independent second-reading section and three genuinely executed Mathlib searches with their actual results and assessed scope. Preserved the first worker's review, the mathematical statement, all four proof steps, and the already correct citations. No mathematical repair was needed.
