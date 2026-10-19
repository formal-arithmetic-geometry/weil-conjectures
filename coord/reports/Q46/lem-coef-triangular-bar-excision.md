# Q46: lem-coef-triangular-bar-excision

## Files written

- dag/nodes/sec-six-functors/lem-coef-triangular-bar-excision.json: item, statement, split into seven proof steps; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-double-mapping-cylinder-space-pushout.json: new statement-only generic topological lemma, unsplit; searched in Mathlib, no match. One new node, zero new Mathlib leaves.
- citations.json: one verbatim statement quotation for each step/node pair.
- searches.jsonl: actual Q46 search receipts. Existing searches in the item have been retained verbatim, including their queries and results; their question has not changed.

## Attachments

None. Searches of WeilConjectures in the slopmaster2 and master checkouts for the exact blueprint tag and for triangular bar/excision terminology found no item declaration. A broader slopmaster2 search for bisimplicial/codiagonal/mapping-cylinder terminology found only an unrelated ring-theoretic codiagonal. There is no claimed attachment, and no compiler was run.

## Sources and WANTED

WANTED: an archived reference for the double-mapping-cylinder theorem for homotopy pushouts of realizations of simplicial sets, for lem-coef-double-mapping-cylinder-space-pushout; and an archived reference for the two-block enriched bar calculation, for lem-coef-triangular-bar-excision. HTT Appendices A.3.2--A.3.3 are only background in the inherited item's source record, not a quoted proof of this formula, and HTT is not present in this checkout's literature directory. I have not represented an absent source as read or downloaded it.

I read the current main-20261015 prop-coef-integral-exceptional-adjoint proof, in particular its displayed middle derived adjunction, and the chapter and the item's assigned unit record. The current proof is a finite-level coefficient-duality argument and does not contain an enriched bar excision theorem. The ancestry records an inherited operadic-extension technical branch. This delivery supplies the technical calculation within that branch; it neither changes a chapter/unit route nor claims that the current blueprint proves the generic topological lemma. The proof is explicitly agent-written. The new node's source identifies this distinction and the missing archival reference. No SGA source is used. No Stacks tag is asserted for the enriched or topological cylinder assertions.

For the topology used in step 5, I read the statements of the existing simplex compactness, Tychonoff product compactness, and compact-Hausdorff-surjection quotient nodes. These already supply the required facts; no new compact-product node was created. In particular the Tychonoff node's source is Stacks 08ZU, label theorem-tychonov, and its statement is for arbitrary topological spaces, not only schemes.

## Statement corrected

Only presentation escaping was corrected: doubled TeX command backslashes and literal backslash-n paragraph breaks were converted to ordinary TeX commands and actual newlines. The formula, all hypotheses, the direction of both module actions, naturality, augmentation, empty-block, universe, and no-cofibrancy clauses are identical. There is no mathematical statement dispute and no weakening.

## Not duplicates

lem-coef-double-mapping-cylinder-space-pushout vs lem-coef-triangular-bar-excision: the new lemma concerns arbitrary continuous maps between three realizations and identifies the cylinder quotient with a coherent pushout of spaces. It contains no enriched category, tensor, module, mixed-word decomposition, or bar comparison. The item must construct and identify the three spaces, both augmentations, and the homeomorphism to its total bar; steps 2--5 carry that argument.

lem-coef-double-mapping-cylinder-space-pushout vs lem-coef-simplicial-realization-cylinder: the existing node identifies |K times Delta^1| with |K| times [0,1], with endpoints. It does not state any pushout universal property or arbitrary span theorem.

lem-coef-double-mapping-cylinder-space-pushout vs lem-coef-relative-categorical-cylinder-criterion: the latter is about equivalence edges in functor quasicategories and a relative categorical cylinder. It neither constructs this topological quotient nor identifies its weak homotopy type with a pushout of spaces.

lem-coef-double-mapping-cylinder-space-pushout vs lem-coef-operadic-collage-comparison: that node treats an infinity-categorical mapping cylinder over an operadic base and its comma-category algebra description. It does not state the topological cylinder theorem. The other enriched amalgamation and three-face nodes are about different simplicial categories or mapping spaces and depend upward on the present branch; none is cited here.

Whole-DAG searches for mapping cylinders, double mapping cylinders, homotopy pushouts, and bar/bisimplicial realization terms were read. The full blueprint search returned no match for “mapping cylinder”, “double mapping”, “homotopy pushout”, “bisimplicial”, or “Tychonoff”; “excision” returned an unrelated algebraic-geometric excision node, and “realization” returned unrelated coefficient realizations. The item blueprint ancestor is prop-coef-integral-exceptional-adjoint. The new node retains the complete inherited via chain and adds this item as its immediate predecessor.

## Mathlib searches

The new cylinder lemma records the six initial Q46 searches, exactly as logged: two distinct LeanFinder phrasings, LeanSearch, Loogle, and greps in Topology and AlgebraicTopology. They all ran successfully. I read every returned type. Ordinary pushout cocones do not imply a derived pushout theorem. Precylinder.trans and Cylinder.trans glue two cylinders on a single object; their source at Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:48--88 and 273--303 does not state the required arbitrary-span homotopy universal property. Those are not one-line specializations. The new lemma therefore stays unsplit, not a Mathlib leaf.

I also investigated whether the elementary join-quotient topology required a new finite-product compactness node. Those subsequent queries and their real results remain in searches.jsonl. LeanSearch/LeanFinder found Pi.compactSpace and instCompactSpaceProd. Searching their declaration names across the DAG found the existing Tychonoff leaf, which is used instead. No duplicate product node is delivered. The simplex compactness and quotient-map leaves were also opened and read.

## Review by Q46

I checked delivery-errors B--E against the actual files. The item has a complete argument, while the only new node has a self-contained statement and empty proof/proof_deps. Its objects, topologies, homotopy types, quotient relation, continuous maps, naturality, and empty cases are all defined or cited in the statement. The generic topological theorem is the missing non-elementary input, rather than a relabelled clause of enriched excision. A proof strategy for it is to use the fact that realizations are CW spaces: the two mapping cylinders give a cofibrant replacement of the span, and their pushout is the displayed double cylinder. Equivalently, maps out of this cylinder into a fibrant space are two endpoint maps together with a path between their restrictions to C, which is the mapping-space universal property of a coherent pushout. This strategy is report material, not a proof inserted into the new unsplit node.

Step 1 uses the actual simplex-colimit statement, the colimit/finite-product clauses of realization-finite-limits, the actual k-space exponential law, and the diagonal-space-colimit cocone theorem. These are the facts needed to pass from iterated topological realization to realizations of diagonal simplicial sets and to homotopy realization. Evaluation on a diagonal preserves colimits degreewise. The product-colimit interchange follows from the exponential-law adjunction, rather than an assumption about arbitrary ordinary topological products. Three directions are handled by repetition, not by a claim about an arbitrary indexing category.

Step 2 uses the explicit enriched bar formula from derived-space-module-coyoneda. The triangular assumption is applied exactly to transitions from O1 to O0. A nonempty word thus has precisely one block cut. I checked p=0 and q=0 separately: the end face removing a whole block is not declared an internal face of M; it is handled by the augmentations in step 3. This avoids a false bisimplicial face at degree zero.

Step 3 uses the single-bar and Fubini clauses of that same node, including its retained-variable and augmentation clauses, and the diagonal-space-colimit comparison. The O1 chain acts contravariantly on Y to define f, and the O0 chain acts covariantly on X to define g. The intermediate module is computed objectwise before taking the second bar. Restrictions of projective replacements are not assumed projectively cofibrant. Instead the cited bar theorem works for the actual restricted modules and requires no local Kan hypothesis.

Step 4 uses only the bar realization definition and its actual face, degeneracy and endpoint action maps. I wrote the formula ((1-t)u,tv), checked both endpoint identifications, and checked that degeneracies add weights. This establishes a map of the genuine bar quotients with the requested inclusions. The homotopy along the middle term is specified, not replaced by an unspecified equivalence.

Step 5 verifies the inverse and topology, rather than saying that a comparison “transports”. The simplex compactness node applies to p, q, and 1; Tychonoff applies to their three factors; the compact-Hausdorff-surjection node applies to the displayed continuous surjection onto a Euclidean simplex. Thus its quotient-map hypothesis is proved. The exponential law makes products with labels preserve the required colimits in k-spaces. This is the precise topology needed for the endpoint identifications, where division by t or 1-t alone would not prove continuity. I corrected the first draft here by explicitly citing these three compactness/quotient facts instead of using them silently.

Step 6 invokes the new lemma only after step 1 proves that U, V and W are realizations of simplicial sets. It takes exactly the cocone and homotopy specified in that lemma's statement. The two-sided bar clause then identifies the total homotopy type. Thus the new lemma does not supply the enriched computation, which has already been proved in steps 2--5.

Step 7 uses the existing retained-variable and composition-augmentation clauses, and checks the coordinate formula itself against functors and actions. No injectivity on objects or arrows is assumed: identifying objects can turn words degenerate, but the bar degeneracy relation already adds their weights. Empty O0, empty O1, both empty, and an empty connecting module all give the stated cylinder quotient. For two terminal blocks with N=point and terminal modules, it is an interval. For N an arbitrary simplicial set it is its unreduced suspension when both endpoint bars are points, as the formula requires. These also test the new lemma at C empty and at A=B=point. General continuous maps in the helper are intentional: its application uses homeomorphisms from the iterated realizations.

Every cited statement was opened, and citations.json copies it verbatim. No use depends on a cited node's proof. The extra topology nodes are Mathlib leaves, so they introduce no off-unit non-leaf tool use. All other proof inputs have the item's unit. No proof step exceeds 2000 characters; the substantial join-quotient calculation is nevertheless reviewed as a comparison, with its topology supplied by the existing generic facts. No non-elementary claim is marked elementary merely because it carries the conclusion.

## Unfinished work

The single new topological lemma is intentionally statement-only, as required by a one-level split. Its later proof is not claimed here. The item itself has no unassigned argument. Delivery remains subject to the required remote checks and independent maintainer review.
