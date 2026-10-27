# Stage-1 delivery: lem-sfb-sheaf-cotangent-ext-representative

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-cotangent-ext-representative.json: item, split in five steps; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-polynomial-differentials-free.json: statement-only supporting lemma, unsplit; no exact or one-line Mathlib match. Its assertion is a natural module-sheaf isomorphism, not the Ext representative assertion.
- citations.json: verbatim statement quotations for every step/node citation.

## Attachments

None. Searched the read-only project under lean/WeilConjectures for the item tag and cotangent/Ext/representative terminology. The ring cotangent declarations found there do not state the sheaf Ext theorem. Existing proof of the free-module adjunction is reused through its existing DAG node, not claimed as a proof of this item.

## WANTED

None: all mathematical sources used are present.

## Findings and corrections

The item statement is faithful to Stacks 08UJ and is unchanged. Its empty proof is replaced by the source's generator-changing argument. The inherited two-term boundary lemma only states exactness at Hom(M,G); it does not give the needed exactness at Ext^1(K,G). Step 2 instead uses the existing Mathlib leaf lem-weil-pbc-hom-out-of-triangle-exact on the cone triangle, and uses the existing two-term node's degree-zero statement to identify shifted heart morphisms with module maps. No stronger property is silently attributed to the boundary node.

The inherited Mathlib grep summary incorrectly listed three Presentation/Differentials hits. Its result text is corrected to the actual logged hit count and paths. Inherited searches and the previous attempt's searches.jsonl are retained; the missing second item phrasing was executed and the already recorded free-differential search results were read and checked against source. No searches were invented. Mathlib's mvPolynomialEquiv is a theorem about rings, not the sheafification comparison for an arbitrary sheaf of variable sets. PresheafOfModules.relativeDifferentials' and isUniversal' are ingredients, not the displayed module-sheaf isomorphism after evaluation.

The latest blueprint unit and direct-image proof were read from literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. This item is a generic deformation-theory input well below the recorded alteration/tangent-space branch, not the unit's key theorem. No unit or chapter file is changed. The inherited blueprint ancestor command returns None; that value and the complete inherited via list are preserved, and the new node prefixes this item in its via list. Blueprint searches for 08UJ, polynomial, differentials, Yoneda, long exact, and free module found no equivalent imported statement for this item or the new sheaf polynomial-differential isomorphism.

## What remains unfinished

The new supporting lemma is deliberately statement-only for a future stage-1 worker. Its future proof should show that maps out of the evaluated differential sheaf correspond to arbitrary maps from E to the underlying B-module sheaf, using polynomial derivations and sheafification, then invoke the existing normalized free-module universal property. This non-elementary comparison has not been hidden as an elementary step or included as a proof in the new statement.

## Not duplicates

lem-sfb-sheaf-polynomial-differentials-free vs lem-sfb-sheaf-cotangent-ext-representative: both cite 08UJ, but the new lemma identifies polynomial differentials with a free module sheaf, for any E and without surjectivity. The item proves existence of changed generators representing an arbitrary derived cotangent Ext class. Neither is a clause restatement of the other.

lem-sfb-sheaf-polynomial-differentials-free vs lem-sfb-etale-algebra-extension-ext: both cite 08UJ in their source material; the existing node classifies square-zero algebra extensions, while the new lemma is the free-module identification for evaluated differentials and has no algebra-extension or Ext classification conclusion.

lem-sfb-sheaf-polynomial-differentials-free vs lem-trf-free-module-sheaf-universal-property: the existing node constructs and characterizes the sheafified free module on E. It does not identify it with polynomial differentials. The new node cites it for that construction and adds the nontrivial identification, with its naturality.

lem-sfb-sheaf-polynomial-differentials-free vs lem-trf-geometric-standard-differential-comparison: the existing node compares standard simplicial differential modules under geometric inverse image. It neither states that the evaluated differential sheaf is free on an arbitrary E nor provides its generator-normalized free-module isomorphism.

lem-sfb-sheaf-polynomial-differentials-free vs lem-sfb-standard-sheaf-cotangent-flat-functorial-model: the existing node gives stalkwise freeness of terms of a specific standard resolution on a topological space. The new lemma is a natural sheaf-module isomorphism on any small site for arbitrary generators, with no point or standard-resolution restriction.

## Review by NU

I read defos.tex Tag 08UJ (lemma-NL-represent-ext-class-ringed-topoi), including both proof paragraphs, for the item and the new lemma. I also read sites-modules.tex Tag 04BL (lemma-universal-module), the construction of the free module sheaf, and Tags 03CN and 03DA for sheaf exactness; derived.tex Tag 0149 and Tags 06XU/06XV for Hom-triangle exactness and the Yoneda comparison; and the Mathlib polynomial differential basis and presheaf differential definitions. I opened every cited node's statement. The citations file copies those statements verbatim, rather than borrowing any content from their proofs.

Step 1 uses exactly the polynomial-presentation comparison to start at E=B and its explicit definitions of K and lambda, and the new lemma to obtain the generator map into F. Evaluation is genuinely sectionwise onto for this initial presentation. No freeness of global sections or projectivity is inferred.

Step 2 uses the derived-category node's explicit cone formula to identify the two-term complex with a cone. Rotation can change the sign of its quotient map; I kept that sign and absorbed it in delta instead of asserting an unchecked convention. The Hom-out-of-triangle leaf gives the required factorization when restriction to F vanishes. The boundary node's degree-zero identification applied to [0 -> M], and the shift equivalence, turn the factor into an actual module map M -> G. Its actual formula for partial then gives the required image. Thus I did not use the boundary node for an exactness clause absent from its statement.

Step 3 uses the module-category statement for abelianness and the computation of cokernels. The Yoneda comparison applies with i=1 to the two heart objects F and G, giving the short exact extension H; it is not applied directly to the two-term object K. The general-site abelian epimorphism lemma applies to the underlying map H -> F after its cokernel is seen to be zero. Its explicit local lifts give local lifts in the sectionwise fibre product E'. This justifies surjectivity of the new polynomial presentation without falsely assuming that a sheaf epimorphism is onto on all sections. Finite limits of sheaves here are checked directly by gluing the two components and their equality.

Step 4 uses the new lemma's explicit naturality for v:E' -> E and the existing free-module universal property to extend E' -> H and check ps=f on generators. The pullback module extension is the sectionwise fibre product with the inherited scalar action; its kernel is G, and the explicit section z -> (s(z),z) is B-linear. The Yoneda comparison's stated naturality and its split-zero clause imply eta f=0. This is the heart of the source's generator-changing argument, and is written in the item rather than moved into a new representative lemma.

Step 5 checks t j'=j f directly from the components of K(v), repeats the exactness factorization established in step 2, and uses precisely the comparison node's equation lambda_E K(v)=lambda_E'. The equality xi lambda_E'=partial(delta) is written before composing with the inverse. There is no unexplained transport of Ext classes.

I tested G=0 and xi=0, zero coefficient sheaves, the trivial sheaf topos, and arbitrary infinite generator sheaves: the zero obstruction permits a split extension, and the fibre product construction never needs a global choice of lifts. For the new lemma E empty gives zero differential and free-module sheaves; the zero ring also gives zero on both sides. No finiteness, enough-points, local-freeness-on-global-sections, or projectivity hypothesis has been added. E' is formed by finite limits in the same universe, so the small-site convention is preserved. Every proof step is under 2000 characters. The one new lemma is a reusable comparison, not an elementary three-line calculation from the existing statements and not a restatement of an item clause.

The cross-unit Yoneda and free-module statements are generic tools, declared in split_report.tool_uses with their precise roles. The Hom exactness and local epimorphism nodes are existing Mathlib leaves. No SGA source, Lean edit, compiler, local check_dag/review_split/preflight command, repository write, or direct git command was used.
