## Files written

- `dag/nodes/sec-six-functors/lem-coef-unstraightening-external-products.json`: statement, split in eight steps; no Mathlib match. Statement unchanged.
- No new nodes and no Mathlib leaves.
- `citations.json`: every step/dependency pair, with verbatim extracts from the two existing statements.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, unstraightening, straightening, pinched cube and Sing_Q/SingQ; no declaration was found. The upstream name table also has no matching name. Upstream master is reference material, not a finished-proof source.

## Wanted literature

WANTED: Jacob Lurie, *Higher Topos Theory*, Section 2.2.1 and Remarks 2.2.2.11--12, especially printed pp. 73--74 and 77--78, archival copy for `lem-coef-unstraightening-external-products`. Read these places online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no document was downloaded and nothing was written under literature/. The remark asserts the canonical external-product isomorphism and its point specialization, without supplying the calculation. The proof here is marked agent-written, and supplies that calculation. No Stacks tag states this simplicial-enriched result. No SGA source is used.

## What was wrong or missing

The imported item had no proof and no project Lean audit declaration. Its statement is correct, including the strict Sing_Q factor over a point, and has not been changed. The source remark leaves the product calculation implicit. I expanded it through explicit simplicial categories and a quotient presentation of the cone pushout, rather than assuming that coherent realization preserves Cartesian products (which is not needed). I replaced the item's inherited search records with searches actually run for N4 by msearch.py. The historical blueprint ancestry is retained, with its place now identifying the current main-20261015 ancestor's coefficient-adjunction paragraph. The unit and chapter records are unchanged; this item is not their key statement.

## Unfinished work

None in this one-level split. The two reused dependencies remain their own items wherever not already split. This report and sandbox are for the fresh second reader; no delivery was pushed.

## Search and duplicate checks

The ancestor command gives `prop-coef-integral-exceptional-adjoint`. Whole-blueprint searches for `unstraightening` and `2.2.2.12` found zero blueprint nodes. DAG searches by these source numbers, external products and collage/cone vocabulary found the existing unmarked straightening, pinched-cube and marked-cone nodes. The marked-cone external-product node is about a comparison of left straightening functors in the marked Cartesian model and proves a weak equivalence, whereas this item is an isomorphism of unmarked right adjoints. It is not a substitute. Since no new node is created, no new-node duplicate pairs arise.

Ran leanfinder, loogle, grep and leansearch using the prescribed command, then a second semantic phrasing. All returned successfully. Loogle and the full-source grep returned zero hits. The semantic searches returned ordinary external products, products of standard simplices, groupoid and profinite cones, conical enriched products, and Cech nerves. I read the signatures and the ordinary external-product source `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean` and standard-simplex source `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean`. The former's `prodCompExternalProduct` concerns ordinary functor composition; neither file defines coherent cone unstraightening. No result states the item or gives a one-line specialization of it. The exact queries and the actual command-log records, with names/digests, are recorded in the item's mathlib_searches; the command log remains in searches.jsonl.

## Review by N4

I read the chapter record, the unit `sk-prop-sf-biduality-general`, the standing brief, delivery-errors B--E, the item and both cited statements in full. I read the current main-20261015 ancestor's separate proof file, paragraph 2 and its following naturality paragraph. This auxiliary lemma supports the inherited enriched-diagram infrastructure under that coefficient-adjunction computation; it changes no unit route. Online I read HTT Section 2.2.1's ordered-cone construction and Remarks 2.2.2.11 and 2.2.2.12. The item has the same arbitrary small bases and arbitrary enriched diagrams as that product assertion. In particular there is no assumption that S is a quasicategory, that D is locally Kan, or that either diagram is fibrant. There are no new statements to test or new-source tags to assign.

Step 1 takes the enriched-action convention from the unmarked-straightening statement and constructs E_F completely. Its only new nonempty compositions are the action of F; associativity and identities are precisely the functor equations. There is no appeal to an existence theorem for a collage.

Step 2 uses the explicit coherent-simplex formula from the pinched-cube statement, not its proof, to check that the initial face is full and that there are no outgoing maps from its last vertex. The unmarked node supplies a and the ordered cone. I checked the types of every generator: h goes i to j, r goes d to a(i), t goes j to v, so both sides of the displayed relation lie in the same mixed mapping object. Simplicial operators and precomposition preserve these generators. This explicitly constructs the quotient in simplicial sets.

Step 3 uses the pushout defining M in the unmarked node. The proposed map to an arbitrary target is J(t) composed with H(r); the relation is respected by agreement on A. Every generator [r,t] is the composite of r with [identity,t], proving uniqueness as well as existence. This proves the universal property rather than citing a generic enriched-Kan-extension formula. It identifies the mixed mapping diagram with the actual L in the cited statement, not an object from that statement's proof.

Step 4 uses exactly the definition of enriched natural transformation and the simplex formula in the unmarked node. The transformation equations give the mixed composition equations for a functor E_R to E_F, and vice versa. Restriction to B and unique pushout extension are inverse. These are direct checks from definitions, as recorded by the elementary flag.

Step 5 pairs the cone functors from step 4. I checked all four types of mapping objects in the indicated full subcategory of E_F times E_G, including outgoing empty sets and the terminal endomorphism object. Its initial restriction is phi boxtimes phi' on the particular simplex (sigma,sigma'); this never identifies C[S times S'] with C[S] times C[S']. Projection and pairing give inverse maps of simplices, not merely a weak equivalence. This short product calculation is a step, not a new node restating the item.

Step 6 takes the restriction rule from the unmarked statement. The formula with C[theta star identity] checks degeneracies as well as faces. A diagram map acts on mixed mapping objects by its components, so diagram naturality is also verified explicitly. The base simplex is unchanged. Step 7 checks the two bracketings on three coordinates and the unit on the unique terminal coordinate; it does not use an unspecified coherence theorem.

Step 8 uses the actual strict fiber-isomorphism clause of the unmarked statement, whose quantifier is every F, and the identical definition of Q in the pinched-cube statement. Thus specializing over a point needs no fibrancy. The ordinary pairing bijection for maps from Q^n commutes with every cosimplicial operator and proves the specialized product compatibilities. This step is marked non-elementary because it applies the existing fiber theorem. Citations.json contains the precise sentences just described for every citation, including repeated ones.

For delivery-errors B--E: there are no new nodes, hollow definitions, relabelled clauses, or new duplicate sources. Every proof dependency exists and the union is precisely the two listed ids. The only auxiliary categories and quotient diagrams are explicitly constructed inside the proof, not introduced as unsplit statement-only nodes with hidden proofs. All substantial identities used from the cited nodes occur in their statements; no proof text of a dependency is used. I checked empty bases/categories (a nonempty base cannot map into an empty indexing category), terminal bases/diagrams, n=0 (the quotient reduces to the representable action), repeated initial images a(i), non-Kan K such as a horn, and arbitrary non-Kan mapping simplicial sets. All formulas remain well-typed. In particular the point factor remains Sing_Q K, and I made no replacement by K. Universe enlargement handles finite coproducts and degreewise quotients; no large diagram is smuggled into a small-colimit assertion.

## Second reading by N4

- Item statement: checked against HTT §2.2.1 and Remarks 2.2.2.11–12, including arbitrary small simplicial bases/categories, arbitrary enriched diagrams, the product over (S\times S'), the strict point factor \operatorname{Sing}_Q K, and the no-fibrancy clauses; verdict: agrees hypothesis by hypothesis.
- Step 1: checked the constructed collage (E_F) against the enriched action convention in `lem-coef-unmarked-straightening-quillen`; verdict: elementary and well typed, with identities/associativity supplied by the functor action.
- Step 2: checked the coherent-simplex mapping objects and quotient relation against `lem-coef-pinched-cube-latching` and the cone definition in `lem-coef-unmarked-straightening-quillen`; verdict: the initial face, empty reverse maps, and simplicial relation are correctly used.
- Step 3: checked the pushout mapping-out argument against the displayed pushout and mixed mapping definition in `lem-coef-unmarked-straightening-quillen`; verdict: universal property and uniqueness are explicitly established.
- Step 4: checked the action-square characterization of enriched natural transformations and the simplex formula in `lem-coef-unmarked-straightening-quillen`; verdict: restriction and extension are inverse and the cited statement supplies the required simplex identification.
- Step 5: checked the full-subcategory product calculation against the cone construction and product clause in `lem-coef-unmarked-straightening-quillen`; verdict: all old, mixed, outgoing, and terminal mapping objects agree coordinatewise, including empty cases.
- Step 6: checked simplex-operator and diagram-map naturality against the restriction rule and action-square clause in `lem-coef-unmarked-straightening-quillen`; verdict: precomposition/postcomposition give the claimed simplicial natural isomorphism over the stated base.
- Step 7: checked associativity and unit compatibility against the product isomorphism in the item and the terminal one-object simplicial category; verdict: the coordinatewise verification covers all bracketings and the unit.
- Step 8: checked the point specialization against the all-diagrams fiber isomorphism in `lem-coef-unmarked-straightening-quillen` and the definition of Q^n in `lem-coef-pinched-cube-latching`; verdict: the \operatorname{Sing}_Q factor and iterated/terminal compatibilities follow without fibrancy.
- Existing-node audit: searched the DAG for the two cited ids and for unstraightening/external-product terminology; verdict: both dependencies are unique and no duplicate or Mathlib leaf is needed.
- Edge cases: checked empty and terminal bases/categories, (n=0,1), repeated initial images, zero/terminal diagrams, non-Kan mapping simplicial sets, and the point factor; verdict: formulas remain typed and unchanged.

Changes made: corrected the node metadata field `created.item` to the delivered item name (the worker record had incorrectly named `lem-coef-simplicial-right-fibration-presentation`). No mathematical statements, proof steps, or citations were changed.
