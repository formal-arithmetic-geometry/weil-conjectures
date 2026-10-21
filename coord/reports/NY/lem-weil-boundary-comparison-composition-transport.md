## Files written

- `dag/nodes/sec-six-functors/lem-weil-boundary-comparison-composition-transport.json`: statement, now split in nine steps; no full Mathlib match. The statement and statement dependencies are unchanged.
- `citations.json`: four verbatim statement extracts, covering every external node citation in the proof steps.
- `searches.jsonl`: five actual Mathlib-search responses from the required search command; their records were added to the item, retaining its inherited searches.
- `write_split.py`: sandbox-only preparation script.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this item is not its unit's statement node.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for composition/comparison/mate/counit terminology. Read `SixFunctors/Etale/Derived/Composition.lean`, the adjunction-composition part of `Etale/Derived/Adjunctions.lean`, and `ProEtale/FiniteCoefficient/Derived/UpperShriekComposition.lean`, particularly lines 195–248 and the ambient counit assertion at 410–421. The etale declarations supply ordinary adjoint-composition results. The pro-etale ones assert existence for a composition isomorphism on preserved full subcategories, or assume ambient pro-etale adjoints. They do not state this specified unit-conjugated map for the given etale mate with the fixed Hom normalization and constant-scalar specialization. None is an exact attachment for the item.

## WANTED

None for this proof. The source PDF and the ancestor's source at the recorded master-blueprint path are present. The main-20261015 path for this ancestor is absent on this clone; I used the actual source recorded by the ancestor and the current DAG statements, rather than treating a missing snapshot as an additional mathematical source.

## Corrections and route

There was no mathematical statement error. The node had no proof. Its source is explicitly agent-formulated: Bhatt–Scholze Corollary 5.1.6 supplies the comparison unit, not the entire displayed mate-transport identity. The proof is therefore marked `proof_origin.by = agent`. The existing bounded-site-adjunction transpose statement supplies the exact single-map normalization; the composition calculation is written out here.

Read the chapter record and `sk-prop-sf-biduality-general` unit record. This item serves the independently formal comparison in the first proof paragraph of `cor-weil-boundary-duality-discharge`, through the already split `lem-weil-boundary-dualizing-composition`, steps 6–7. It does not supply a replacement route for biduality. No prohibited SGA route is cited. Four off-unit comparison tools are explicitly declared in `split_report.tool_uses`: site-comparison unit, derived pullback typing, bounded Hom/counit normalization, and inverse image of constant coefficients. These are the comparisons already used in the item's statement, not alternate proofs of its unit.

## Searches and reuse

Whole-DAG searches covered the exact item, the bounded-site-adjunction and compact-support-comparison identifiers, comparison-unit terminology, and the displayed transported mate terminology. `tools/blueprint_refs.py ancestor` returns `cor-weil-boundary-duality-discharge`; searches for `composition mate` and `comparison unit` return no equivalent blueprint statement (the latter returns only `det-pe-classical-sheaves-unit`, a sheaf-level unit result). Thus `same_as` remains empty. Existing `lem-pur-bounded-site-adjunction-transpose` already states the normalized relative counit equation and naturality, so it is reused rather than creating an overlapping node. `lem-sf-class-compact-support-comparison` gives invertibility on etale-origin inputs; the stronger bounded-site statement already includes the particular natural B used here, so no redundant proof dependency was added.

Actual searches were two differently phrased LeanFinder queries, one LeanSearch query, one Loogle query, and a Mathlib grep through the prescribed command. All services answered successfully. Read the results and the source of the relevant generic candidates in `Mathlib/CategoryTheory/Adjunction/Mates.lean:265–295` and `Adjunction/Basic.lean:565–586`: they give generic conjugation/counit formulas and the counit of a composite adjunction, not the specified etale-to-pro-etale comparison-unit formula with its chosen relative Hom chain. It takes the explicit calculation below to relate these structures; the whole item is not a one-line specialization. All five queries, their exact results and negative verdicts are recorded without fabricating searches. No new node is declared absent from Mathlib.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish.

## Review by NY

I read Bhatt–Scholze, *The pro-etale topology for schemes*, PDF page 35, Corollary 5.1.6, including its restriction to bounded-below inputs and the adjacent warning about arbitrary unbounded complexes, and page 37, Proposition 5.2.6(1–2). The corollary states invertibility of the actual comparison unit. The stronger module-coefficient version needed here is precisely the statement of `thm-weil-pbc-site-comparison`, which I opened and read in full. It applies to finite discrete rings and ordinary left module sheaves, with no constructibility assumption. The coefficient A in the item is exactly this ordinary finite ring; I have not silently replaced it by continuous-function coefficient modules. The parent and ancestor statements and the ancestor's complete source proof were also read. No new node has a source needing review.

For step 1, I checked the actual unit-isomorphism formula in `thm-weil-pbc-site-comparison`, and the D-plus preservation clause in `def-sf-comparison-derived-pullback`. Applying a functor to an inverse pair proves invertibility of rho without an additional theorem about exceptional pullback. The hypotheses already assume R_h preserves D-plus; I use this for R_g H, R_f R_g H and R_gf H. The target of rho is bounded because it is isomorphic to that bounded source. This does not assert boundedness from a comparison theorem on unbounded inputs.

For step 2, I read the entire statement of `lem-pur-bounded-site-adjunction-transpose`, including its explicit Phi, definition of B, counit equation and naturality. Its C, F_e, F_p and f-times match S, F_h, P_h and R_h, using the same compactification. Our schemes satisfy its finite-type hypotheses, our maps its separatedness and finite-type hypotheses, and each finite-dimensional compactification admits an integer dimension bound. The extra boundedness R_h J required there is an assumption here. Its formula is exactly the formula used, so this cites a statement rather than an argument hidden in the node's proof. The relative counit is fixed by the same Hom bijection; no arbitrary adjunction structure can intervene.

Steps 3 and 4 use only inverse-pair cancellation, functoriality and naturality of the transformations fixed in the statement and steps 1–2. I checked the types of all four factors of Xi and all four of alpha-p. In particular t has source K = R_gf H and target L = R_f R_g H; reversing Xi gives Q_f(r) b S_X(t), in this order. The expression in step 4 follows by cancelling B_gf against its inverse, not by assuming the pasted identity.

Steps 5–8 carry the substantive composition calculation, without citing a restatement of the item. Step 5 uses the stipulated naturality of mu_f specifically at r = rho_g,H; the two targets are bounded below. Step 6 substitutes the single-map counit equation from step 2 at (g,H) and (f,R_g H). Step 7 writes all three B-naturality squares explicitly: at epsilon_f,R_g H, at theta_H, and at F_f(theta_H). I checked each source and target: epsilon_f,R_g H goes from F_f L to R_g H, and F_f(theta_H) goes from F_f K to F_f L. These squares require only naturality of the same B from step 2. They yield the image under S_B of the pasted etale counit. Step 8 then uses the mate equation assumed in the item, at K = R_gf H, and obtains exactly the left-hand expression of step 4. The elementary labels mean these are displayed naturality equalities and substitutions from already cited facts, not an uncited geometric compatibility theorem.

For step 9, I read `lem-pe-constant-left-module-inverse-image`, including its scalar-preserving constant-ring identification, action on module sheaves, and termwise passage to derived categories. The degree-zero constant module is bounded below. Substitution H = A_e turns the first and last rho into the two stipulated lambdas and gives exactly the requested four-arrow formula, with the canonical identification S_B A_e = A_p.

I tested the formal argument when all comparison units and B maps are identities: Xi becomes theta inverse, alpha-p becomes alpha, and the claimed equality becomes the given etale mate equation with the stated orientation. For identity f or g the same cancellation works, without assuming a separately normalized identity compositor. At H = 0 and on empty schemes all displayed maps have zero source/target as appropriate and all inverse pairs remain valid. At n = 1 nothing changes; no invertibility of a uniformizer or field property of A is used. No common cohomological bound or constructibility of arbitrary inputs is smuggled in.

I checked delivery-errors B–E against the files: no new statement-only node is necessary; the original statement is retained, all mathematical notation is TeX, the blueprint origin is precise, and every cited external statement has a verbatim extract in citations.json. The proof does not create clause-sized nodes, use the proof of a cited node as an API, introduce a cycle via the immediate parent, or assume an ambient pro-etale adjunction. Every step is under 2000 characters. The only changes to the original are its completed proof, proof metadata, search records and precise blueprint place.

## Unfinished work

None in the natural-language split. No Lean was written or compiled. Server dry run and direct delivery are performed after this report is written.
