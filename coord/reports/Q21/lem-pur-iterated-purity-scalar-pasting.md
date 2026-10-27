# Stage-1 report: lem-pur-iterated-purity-scalar-pasting

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-iterated-purity-scalar-pasting.json: item, statement, split using ten existing dependencies; no Mathlib match.
- citations.json: verbatim statement quotations for every step citation.
- searches.jsonl: actual msearch records; prepare.py: sandbox-only reproducible JSON preparation.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, iterated purity, purity/scalar and purity/composition. Read Smooth/Reduction.lean and Smooth/Transport.lean. Reduction.map_smoothPurityIso_hom_comp treats a single finite-coefficient square with additional constituent-compatibility hypotheses; it does not state either whole item on rational constructible coefficients. Transport does not supply this compositor and horizontal-pasting theorem. No exact finished declaration was found.

## WANTED

None for this split. The proof is an agent expansion of the current blueprint's transport paragraph, using existing DAG statements as the lemmas; it does not assert that Stacks states this rational purity theorem.

## Corrections and scope

The statement is unchanged. The imported item had no proof. The split supplies its argument rather than extracting its two conclusions as new nodes. The first equality needs the actual canonical compositor, not any isomorphism with its endpoints. The second equality needs naturality twice, not just the phrase horizontal pasting. Both issues are addressed explicitly. The root/power and shift constituents are retained, including the ordered blocks e,d and the zero-exponent unit.

The existing scalar-naturality node has a historical SGA note in its own source metadata. This delivery neither adds nor follows an SGA source: the actual proof uses the stated comparisons through lem-pur-rational-normalized-purity-diagrams and the blueprint/Stacks representative calculus. It does not change the locked finite-purity route.

## Not duplicates

No new nodes. Whole-DAG searches for twist/composition/scalar, the blueprint searches for twist, scalar.*composition, twist.*scalar, twist.*add, iterated purity and scalar pasting, and the nearest-blueprint-ancestor query were read. The existing cochain, completed realization, integral line and shift nodes suffice.

## Mathlib searches

Retained the item's inherited searches and added the actual six Q21 msearch records. LeanSearch returned module scalar extension, polynomial laws and ordinary presheaf pullback; Loogle returned NatTrans naturality; LeanFinder returned sheaf-module pullback composition and abstract shift functors. The first semantic search's full output was read before interruption. The interrupted second search completed: its durable log contains eight hits, including Functor.commShiftPullback and Pullback.Triplet.tensorCongr_trans_hom. Read the local source for the shift machinery and Scheme.Modules.pullbackComp at Sheaf.lean:241. These are building blocks, not this rational constructible Tate/purity statement. The AlgebraicGeometry grep for purity|TateTwist returned no hits; the second grep found ordinary Scheme.Modules.pullbackComp. No search was invented, and no unavailable service is called a negative result.

## Review by Q21

I read the current main-20261015 prop-pur-rational-purity-trace-coherence proof paragraph and the current sk-thm-purity-transport statement, alongside the chapter/unit records and SETUP's three-level route. The item is a subordinate calculation in coefficient transport and does not change the unit or chapter. I read Stacks sites-cohomology.tex at lemma-derived-pullback-composition (0D6D) and lemma-pullback-tensor-product (07A4), including their common flat-term K-flat model arguments, and sites-modules.tex lemma-tensor-product-pullback (03EL). These support the representative calculus already stated by the cited nodes; they are not substitutes for node citations. There are no new-node sources to audit.

For step 1 I read the whole statement of lem-pur-rational-normalized-purity-diagrams. It explicitly gives every integral representative's uniform finite-Tor domain, natural rational comparisons, the single-purity square and unit/tower/shift laws. I use its single-purity square, not its exceptional compositor formula, so the argument does not assume the scalar pasting to be proved.

For step 2 I read prop-weil-pbc-scalar-extension: its last sentence explicitly makes the actual pullback comparisons compatible with composition, successive fields and shifts. I use this for the untwisted compositor only. The categories in the item's statement are precisely its raw rationalized categories; their scheme-domain assumptions are included in def-weil-pbc-rational-category, which was also read. The schemes are finite type over k, and the distinct primes ensure invertibility of ell. No claim about arbitrary constructible direct-image preservation is taken from this proposition.

For step 3 I checked all three cited statements. The cochain node includes both the geometric composition tensor square and coefficient tensor square, as chain maps. The normalized-scalar-realization node identifies the specified completed scalar maps, not merely isomorphic values, with total-limit images of those derived-system maps. The tower-substitution node explicitly identifies completed associators, symmetry, composition and substitution. Thus the proof applies a functor to an equality of whole-system morphisms and conjugates by specified natural identifications; it never infers equality from equal reductions and never assumes a ramified residue-ring extension is flat.

For step 4 I read clauses 3 and 4 of lem-pur-integral-twist-line-inverse-image and the tensor-power clause of lem-weil-integral-twist-base-change. They give the actual roots-induced line comparison and its coefficient square and scalar tensor-power map. The explicit recursion is zero/one/successor, so no separate exponent-addition lemma is hidden. The cochain node supplies the reassociation and block symmetry needed in the induction. Every tensor symbol in the displayed calculation is generalized local tensor notation; equality follows from the balancing relation, so the argument does not require a global trivialization or equality detection on stalks of the rationalized category.

For step 5 I read lem-pur-derived-tensor-additive-constraints for its precise (-1)^(si) and Koszul normalizations and representative full faithfulness, and lem-weil-completed-scalar-chain-shift for its actual Roos cone shift, including the second-coordinate sign. The shifts here are even and lines are in degree zero. The same tensor reindexings occur on both routes after an input shift. This is why the sign simplification is valid; it is not an appeal to an unspecified coherent choice.

For step 6 I read all eight defining factors of def-pur-composition-comparisons. It fixes the finite compositor rather than arbitrary endpoints, and the tower-substitution statement identifies its completed factors. Pasting steps 2--5 gives the boundary equation with exactly A and a_gf. The computation is performed in that fixed order, with inverses handled by cancellation, and then rationalized.

For step 7 the first use is the f square evaluated at G_gK; naturality of a_f is used at gamma_g. The next naturality square is gamma_f at b_g. Only then is the g purity square substituted inside H_f. The quoted normalized-purity statement supplies each of these natural transformations on the required rational domains. I checked the intermediate objects: T_YG_gK and G_gT_ZK are in the Y category, so the b_g naturality move is typed. The output of both chains is G_fG_gT_ZK.

For step 8 I checked the tower law by substituting into w_FG=F_L(w_G)w_FG_E. Naturality moves the one middle pair, leaving the input/output associators and cancelling the internal ones. This applies to A and beta; identities use their given unit maps and shifts use step 5 and the normalized-purity shift equations. Consequently the final coherence assertion has a calculation, not the unsupported word transports.

I tested E=L, d=0, e=0, d=e=0, an identity geometric morphism, the zero input, and empty schemes. The powers use coefficient units at exponent zero, all zero-object maps are unique, and no nonempty, connected, proper, unramified or global-basis assumption enters. Generic tensor/line/shift tools from other units are declared in split_report.tool_uses. I checked the dependency closure for a path back to this item and found none. No step exceeds 2000 characters; each elementary step is a displayed calculation or pasting of the previously established constituent equations. The B--E audit found no new-node form, duplicate, hidden-clause-node or uncited substantial auxiliary assertion requiring a new node.

## Unfinished work

None within this one-level split; all lower statements are existing DAG nodes. Required server dry run and delivery are performed after this report.
