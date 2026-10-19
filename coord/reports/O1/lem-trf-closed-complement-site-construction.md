# Worker report: lem-trf-closed-complement-site-construction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-closed-complement-site-construction.json`: statement, split; no Mathlib match for the whole construction. The statement, its statement dependencies, its ancestry, its source and all inherited search records are retained. Eight proof steps and their exact dependency union are supplied; five actually logged searches are appended.
- `citations.json`: one literal statement quotation for every node cited in every proof step.
- `report.md`: this report. `searches.jsonl` is the search command's own log. `write_split.py` is a sandbox-only preparation script, not a project change.

New nodes: **0**. New Mathlib leaves: **0**. Three existing Mathlib leaves are reused: `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`, and `lem-weil-pbc-sheafification-sets-exact`.

## Attachments

None. Searches in the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint id, closed-subtopos terminology, subterminal/Subterminal and closedComplement found no declaration stating this general small-site construction. The closedComplement hits concern schemes and their open/closed module operations, not arbitrary subterminal sheaves and modified Grothendieck topologies. No compilation was run. No upstream-master sorry declaration is used as a completed proof.

## WANTED

None. All sources actually used are in `literature/stacks-project/sites.tex`.

## What needed repair

The item had a correct, self-contained statement and no proof. Stacks 08LY (`lemma-closed-subtopos`, lines 10176–10237) omits the argument that a J-sheaf terminal over U satisfies the finer sheaf condition. Step 6 supplies that argument, including uniqueness of amalgamation; it does not turn that clause of the item into a new node. The topology axioms are checked directly on sieves, avoiding any additional epimorphic-family hypothesis from the good-site presentation used in the printed source proof.

The original statement already correctly assumes subcanonicity only for J. No STATEMENT-DISPUTED, source error or hypothesis change is needed. No unit or chapter file is changed. The node is not the unit's statement node. The main-20261015 ancestor proof and the unit `sk-i-curve-zero` retain the normal-cone specialization route. This item supplies the topos construction used in step 3 of the existing `lem-trf-topos-complement-factorization`, in that source-localization branch; the parent is not cited as an input to its child.

## Unfinished work

None for this one-level split. No new unsplit nodes are needed. The independent maintainer review remains part of the delivery process.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for closed subtopos, 08LY and the modified topology find the existing parent and source-localization consumers, rather than an independent proof of this site construction. In particular `lem-trf-topos-complement-factorization` already depends on this item, so citing its more general topos statement back would create a cycle. The three existing generic site lemmas are reused rather than duplicated. `blueprint.same_as` stays empty.

## Review by N1

I read the whole B–E checklist in `coord/delivery-errors.md`, the worker brief, the three blueprint levels in SETUP, stage 1, GOAL, dag-sync, the chapter and unit records, and the main-20261015 proof of `lem-trf-local-term-locality`. For the mathematical source I read Stacks 08LY in full, together with 00Z4 (topology and the definition node quoting it), 00WX/00WH (the sheaf adjunction), 00W2 (sectionwise limits), 00WJ (left exactness), and the topology version 00ZM. There are no new nodes needing separate source review. I also read the complete statements of every cited node before forming the citation quotations.

Steps 1–2 use only `def-weil-pbc-topos`: its sieve and topology axioms say exactly what is checked. The sieve O_V consists of arrows whose domains map to U; the pullback identity follows from the product universal property. In the transitivity check it is essential to apply J-transitivity to S union O_V, not just S. For arrows in O_V the pullback of T is maximal. I checked this explicitly rather than appealing to the source's sheaf-epimorphism argument, which uses a stronger presentation convention.

Step 3 also uses only the topology definition. It writes the elementary generated-sieve, covering-family and full-inclusion arguments out. All pullbacks exist because the item's category has finite limits, and all covering families are small because its arrows form a set. The comparison with covering-family sites is included specifically because the adjunction node in step 7 requires that convention. No comparison theorem is being imported without a node: extending a compatible family to a generated sieve is restriction along its generating factorization, and equality for two factorizations is the compatibility on their fibre product.

Step 4 uses `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, whose statement explicitly says that the presheaf limit is a sheaf and a limit in the sheaf category. Taking a diagram of two objects gives the product being computed. The original J-subcanonicity gives F=h_U as a sheaf. Since U to X is mono, its Hom sets have at most one element. I checked both cases of the component projection (empty Hom set and singleton Hom set), and supplied the explicit inverse U times W to W when W maps to U. This proves the support criterion rather than citing a Yoneda theorem with inadequate statement.

Step 5 uses the literal unique-amalgamation sheaf condition in `def-weil-pbc-topos`: the empty sieve on an object over U is J_c-covering and has one empty matching family, so its section set is a singleton. Step 6 uses that same definition to extend a matching family from R to R union O_V. On the added domains, and on all their restrictions, section sets are singletons. Thus the extension agrees on the intersection and is compatible; J-gluing gives existence, and singleton restrictions on O_V give uniqueness even when R is empty. This fills the exact point where 08LY says 'argument omitted'. Both steps are direct checks from the definition and previous steps, not independent lemmas hidden behind source citations.

Step 7 uses the full statement of `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`: it supplies the adjunction and the explicit colimit-then-sheafification formula. The source and target sites are in the right order, namely identity from (C,J) to (C,J_c), and continuity is precisely the J_c-sheaf to J-sheaf implication proved in step 3. The indexing category is small, and (W,id) is initial in I_W, hence terminal in I_W opposite. I checked the variance by writing the cocone s at (V,phi) to G(phi)(s) in G(W); this proves that the presheaf inverse image is the identity without any extra cofinality theorem.

Step 8 uses the same sectionwise-limit node, `lem-weil-pbc-sheafification-sets-exact` (its statement actually asserts preservation of all finite limits, not just products), `def-weil-pbc-topos` for the small-site topoi, and `def-trf-geometric-morphism` for precisely the left-exact adjoint-pair datum. Both generic theorem nodes are Mathlib leaves and may be used across units. There are no off-route non-Mathlib statement tools, so split_report.tool_uses is empty.

Small cases checked: U=X makes O_V maximal, every sieve J_c-covering and every sheaf in the image terminal, exactly as F=1 requires. On the opens of a space, U empty makes O_V the sieve generated by the empty open; adjoining that empty member does not change covering families, so J_c=J and every G satisfies F times G=F. A one-object terminal category with its minimal topology necessarily has U=X and gives the terminal closed-complement topos; with the maximal topology both sheaf categories are already terminal. Empty covers and objects already empty-covered for J cause no exception: their sheaf condition already forces singleton sections. I did not assume a strict initial object in an arbitrary finite-limit category.

Checklist B: no new definitions, hollow objects, ambiguous tags or statement-only children; TeX is stored once and every search record is retained honestly. Checklist C: each cited statement was opened, all external theorem uses are the three existing leaves, and all other arguments are explicitly written from the definitions. Checklist D: no restatement child and no dependency on an ancestor; the steps carry the actual topology, gluing and adjunction argument. Checklist E: smallness, finite limits, monomorphism, original subcanonicity and sheaf-adjunction hypotheses are all used where needed, with no subcanonicity assumption for J_c. Every proof step is shorter than 2000 characters; I checked the longer elementary steps for hidden subclaims and each is a direct definition calculation. No SGA source, coefficient-category comparison, target alteration, Lean write or compiler was used.

Mathlib searches: I read the inherited recorded results and preserved them. This sandbox ran LeanFinder with two phrasings, Loogle with fully qualified topology/sheaf names, LeanSearch, and the prescribed source-grep search. They returned canonical/finest topologies, the classifier of closed sieves, basic sheaf inclusion and terminality facts, and subterminal objects, rather than this modified topology with its complete essential-image theorem. I read the relevant Canonical.lean and Closed.lean definitions (closed sieves are not a closed subtopos), and the existing leaves' implementations in Limits.lean, Pullback.lean and Sheafification.lean. All five added searches correspond exactly to searches.jsonl; no unavailable service was recorded as a negative result.
