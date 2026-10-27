# Stage 1 report: lem-route-inverse-image-module-lift

## Files written

- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-module-lift.json`: statement, split; no exact Mathlib match. Seven explicit elementary construction/checking steps replace the empty proof.
- `citations.json`: one verbatim statement quotation for each step/node pair.
- No new DAG nodes and no Mathlib leaves were created. `searches.jsonl` is the unmodified command-generated log; `write_split.py` is a sandbox-only writing aid.

## Attachments

None. Searches for the blueprint tag and AlgebraicInverseImage in `lean/WeilConjectures/` find no matching declaration. The existing topological inverse-image module constructions concern continuous maps of spaces; MapMod concerns internal module objects and does not itself give the stipulated sectionwise arbitrary-site presentation with the given e_R. They do not attach this item.

## WANTED

None. The source was available locally.

## Corrections and provenance

The statement is retained verbatim, including its common-universe and small-site hypotheses. No STATEMENT-DISPUTED issue was found. Its old source field cited both 03D2 and 03D7: I read both in `sites-modules.tex`. The actual construction is 03D2 (`lemma-pullback-module`); 03D7 (`lemma-adjoint-pullback-pushforward-modules`) concerns an additional ringed module adjunction that this item does not assert. The source field now explains that distinction. The operation checks fill in the details omitted by the very short 03D2 proof.

The prescribed archive-list command found no earlier attempts, and there was no item, report or search log in the initial sandbox. There is no item-specific repair note. I copied the live unsplit item without changing its statement or inherited metadata. The four 2026-10-27 search entries inherited from its NB-created node remain intact: they are prior evidence, not searches claimed by ND. My fresh command-generated records are appended separately and are all dated by their UTC log timestamps. The generic-term phrasing was a second semantic search, not evidence for a new node.

The actual Mathlib candidates were inspected in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, lines 39–63: `pullback` uses a continuous site functor, a coefficient map and an existing adjoint. It does not supply the comparison and operation-graph formulas for arbitrary L in this statement. The directory grep gives the actual path and lines 53, 60, 106; an earlier single-file grep printed malformed file labels because rg omitted the filename, and this is stated in its search entry. The Loogle query `CategoryTheory.Functor.prodComparison` returned an unknown identifier, and is recorded as an unsuccessful query, not evidence of theorem absence. The other Loogle query succeeded. No service was unavailable in the completed searches.

The whole-DAG keyword/tag scan and blueprint searches for module lift and finite-product preservation found no exact duplicate of this item. Existing finite-product ring transport and abelian-group lifting are related, but do not themselves construct this sectionwise module lift. I read their statements and avoided taking their proof internals as black boxes. The common finite-product term calculation is written in step 3 as an elementary structural induction, so it is not made into an unnecessary new lemma node.

The inherited blueprint ancestor is `sk-thm-rationality`, reached through the compact-support realization nodes recorded in `blueprint.from.via`. I read the fixed chapter and stored unit records, and the newest blueprint's corresponding `det-thm-rationality.md` and `.proof.md` under `latest/blueprint/sec-zeta-weil/sk-lem-wweil-integer-rationality/`. This is an auxiliary algebraic construction beneath its separated-case compact-support realization; no rationality theorem or unit route is replaced. There is no equivalent blueprint node to enter in `same_as`.

## Unfinished work

None in the requested one-level split. The proof constructs the functor and its natural underlying-sheaf isomorphism and verifies the full graph clause. Stage 2/3 and compilation are outside this assignment and were not performed.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by ND

I read the item against Stacks 03D2, including its proof that inverse image applies to the action map through preservation of products. I also read 03D7 to check that an adjunction or tensor-extension conclusion was not being substituted for the construction asked for here. The given ring isomorphism e_R is used in the direction L|R| to |A| throughout; the action formula therefore uses e_R inverse on its input. The module comparison has the opposite direction, but is the identity because the underlying module sheaf is constructed to be L|M|.

Step 1 cites the product definition for projection uniqueness and the site definition for set sheaves and natural-transformation morphisms. I verified that these are in their statements. The existence of sectionwise finite products is proved there by coordinatewise gluing, and invertibility of the comparisons is exactly the item's finite-limit hypothesis. No theorem that presheaf limits preserve sheaves is being silently invoked.

Step 2 uses the full sectionwise module definition, which actually gives the semilinear restrictions and hence naturality of the action. Its addition, zero and negation are natural because the restrictions are additive. The fixed e_R and the hypothesis on its four ring operations give the conjugated ring operations. Uniqueness of additive inverses proves the omitted negation compatibility, without a further hypothesis.

Step 3 cites only projection uniqueness from the product definition. I checked each line: projection is the variable case; pairing naturality and functoriality give the operation case; the unique terminal map handles constants. This is a written elementary induction on finite expressions, not an appeal to an uncited algebraic-theory result. In particular it handles repeated variables, both bracketings and the empty product. This is why a standalone term-transport node would be an unnecessary elementary node.

Step 4 applies that explicit calculation to the eight displayed group/module laws. I checked the types and contexts of all eight; the ring sort is the actual A, not a newly chosen isomorphic ring. The cited module statement supplies those source sectionwise module structures, and source equality on all sections is equality of natural transformations. The zero/negative scalar identities are proved by cancellation on the resulting target abelian groups. This is an elementary computation, with no preservation of module exact sequences or tensor-flatness used.

Step 5 cites the module definition's actual semilinearity condition and writes it for every restriction. The abelian-sheaf condition follows from the already existing sheaf of sets with the new natural operations: gluing is exactly the same unique gluing of elements. This gives an object of the stipulated module category, not merely an abstract internal module.

Step 6 cites that definition's linear morphisms and the product definition. I checked all three morphism equations and the common ring-coordinate comparison; applying the product formula proves A-linearity. Functoriality is L's identity/composition laws, and naturality of the identity e_M follows from the selected underlying map L(h). There is no choice of a fresh comparison for different modules.

Step 7 cites the algebraic inverse-image definition's graph conditions and the product definition. I checked the generalized test sheaf T, not only representable or global sections: the equations are morphism equations on L(T), so taking any target object's sections gives exactly the required graph clause. I checked addition, action and zero explicitly; the ring's addition, multiplication, zero and one use the given e_R hypothesis and the identical calculation. Thus the data have exactly the e_R demanded by the item.

Against delivery-errors B–E: there are no statement-only new nodes to contain hidden proofs, duplicate clauses or wrong hypotheses. The item remains self-contained with its definition references; TeX uses single semantic backslashes. The source tag and label were read, not guessed. Every cited node was opened and only its statement is quoted in citations.json. No proof internals, uncited non-elementary theorems, off-unit statement tools, or new dependency cycles are introduced. The argument constructs the operations rather than relabelling a clause as a new node. Every step is below 2000 characters and is one routine construction/calculation, with the product induction written out.

For small cases I checked L = identity with e_R = identity (the construction returns the original operations and morphisms), a nonidentity ring isomorphism e_R (action is restriction along e_R inverse, not along e_R), the zero module (terminal/zero formulas still hold), the zero ring (the one-action and zero-action equations force the target module to be zero), repeated variables in the distributivity contexts, and empty-cover/empty-product conventions. None requires enough points, flatness, or exactness of a module functor. All writes were confined to the assigned sandbox; no Lean was written or compiled, and no repository git command or local forbidden check was run.
