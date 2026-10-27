# Stage-1 report: lem-sfb-field-groupoid-point-lift

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-point-lift.json: item, statement unchanged, five proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-large-algclosed-field-extension.json: statement, unsplit; no exact Mathlib match for the cardinal overfield existence assertion.
- dag/nodes/sec-six-functors-basics/lem-sfb-small-field-embeddings-conjugate.json: statement, unsplit; no exact Mathlib match extending the prescribed embeddings under the cardinal bound.
- citations.json: verbatim statement excerpts for every use in each numbered proof step.
- searches.jsonl: actual msearch.py searches, retained without editing.

Two new nodes, zero new Mathlib leaves. Existing Mathlib leaves are reused.

## Attachments

None for the item. Searches of lean/WeilConjectures by blueprint tag, 04LR, field/groupoid combinations, and the field-automorphism terminology found no declaration stating the item. The existing `exists_algEquiv_extending_separableClosure` in WeilConjectures/FieldTheory/GaloisAutomorphismExtension.lean extends an automorphism of a separable closure over a fixed base. It does not compare two arbitrary embeddings of a possibly transcendental field into a larger field, so it cannot attach either new input. Its proof was read, including the IsAlgClosure.equivOfEquiv use.

## WANTED

None. All mathematical sources used are available locally. No SGA source is used.

## Findings and corrections

The item was unsplit, with no proof. Its statement agrees with both enumerated conclusions of Stacks 04LR (more-groupoids.tex, lemma-groupoid-on-field-explain-points). No finite-type, algebraicity of the given residue extension, separability, or perfectness hypothesis may be added. The restriction has two separately changed object factors, not just scalar base change of an R-scheme over a single chosen structure map. This distinction dictates the triple constructed in step 3.

The blueprint ancestor command prints `a node created for lem-sfb-field-groupoid-point-lift has blueprint.from.node = None`. The item already has a null ancestor and a full via chain. These are retained, and the new nodes extend that chain, with precise 04LR proof clauses appended to from.place. Current blueprint/latest chapter and unit texts and the direct-images proof were read: this supporting input lies below the inherited proof-(3) alteration/quotient chain. The live unit record is an older sec-six-functors record whereas the current blueprint places it in sec-six-functors-basics; no unit or chapter file is changed here.

The source's field-construction paragraph has a typographical reference to extending to tau on kappa(alpha) in (2). Its intended embedding is sigma from kappa(r). We avoid that notational slip by choosing an overfield of E=kappa(r) directly, and then setting the k-structure to sigma composed with s*. This is the same large-field construction and retains all hypotheses and conclusions.

## Search and reuse

The whole DAG was searched by 04LR, transcendence degree/basis, large transcendence, small subfield, extension of automorphisms, and algebraic-closure statements; all candidate statements, not their proofs, were compared. blueprint_refs.py searches for `field groupoid`, `04LR`, `transcendence`, `automorphism`, `field automorphism`, `large transcendence`, and `algebraically closed extension` found no duplicate. The matching curve-invariance and Frobenius nodes concern different assertions. Existing nodes for transcendence-basis existence, algebraic closure over a basis, and algebraic-closure existence/uniqueness do not assert either cardinal construction or extension of two prescribed embeddings. Existing nodes lem-weil-pbc-morphism-from-spec-field, lem-weil-pbc-residue-field-point-naturality, def-weil-affine-spectrum, def-pc-fibre-product and def-a1-groupoid-scheme provide the geometric ingredients without any new geometric node.

For each new node, msearch.py ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle and grep. The exact queries and original log records are in mathlib_searches. For the item, Q57 also ran all four search tools. All services returned successfully. Mathlib/FieldTheory/IsAlgClosed/Classification.lean:48-72 and Basic.lean:445-489 were read: equivOfTranscendenceBasis requires equipotent bases to have already been supplied; equivOfEquiv requires algebraic closures over the compared bases. Neither discharges the small-field cardinal argument. The classification isomorphisms do not assert that an arbitrary prescribed embedding is extended. AlgebraicClosure alone gives an algebraic extension, hence does not supply the large transcendence bound. ModelTheory/Algebra/Field/IsAlgClosed.lean was also inspected: categoricity is about unspecified isomorphisms, not this relative extension. No partial hit was recorded as an exact match.

## Not duplicates

lem-sfb-large-algclosed-field-extension vs lem-sfb-field-groupoid-point-lift: the new assertion is pure field-overfield existence with a cardinal bound, with no schemes, two residue maps, or lifted point; it supplies only construction (1) of the source proof.
lem-sfb-large-algclosed-field-extension vs lem-sfb-field-groupoid-open-image-closed: the existing assertion concerns an open image in a field groupoid being closed; it does not supply large overfields.
lem-sfb-small-field-embeddings-conjugate vs lem-sfb-field-groupoid-point-lift: the new assertion extends two given field embeddings inside a given sufficiently large algebraically closed field; it asserts no existence of that overfield or any geometric point.
lem-sfb-small-field-embeddings-conjugate vs lem-sfb-field-groupoid-open-image-closed: extending prescribed embeddings is a field-theory tool, distinct from the existing topological assertion about the image of a groupoid morphism.
lem-sfb-large-algclosed-field-extension vs lem-sfb-small-field-embeddings-conjugate: the first constructs an overfield and a size bound; the second starts with an overfield satisfying that bound and constructs an automorphism.
lem-sfb-small-field-embeddings-conjugate vs lem-sfb-large-algclosed-field-extension: the automorphism conclusion and its two prescribed embeddings do not occur in the overfield-existence statement.

## Review by Q57

I read Stacks more-groupoids.tex:1040-1123, Tag 04LR, both its statement and its entire field diagram and three-part proof, against the unchanged item and both new files. The first new statement makes 'very large transcendence degree' precise. For any E, choose a set I of cardinality strictly greater than max(aleph0,|E|), form the rational function field E(T_i), and take its algebraic closure K. The variables remain algebraically independent over E and therefore over the prime field, giving the displayed strict bound. This is an actual independent field-construction lemma, not one of the geometric conclusions of the item.

For the second new statement I checked the source's construction (3) hypothesis by hypothesis. The images a(F), b(F) contain the same prime field P, and the prescribed isomorphism a(x) to b(x) fixes P. Its extension to the relative algebraic closures of these images inside K exists by uniqueness of algebraic closures. The prime-field transcendence degrees of these closures are bounded by |F|. If lambda=trdeg_P K exceeds max(aleph0,|F|), the tower formula forces the complementary transcendence bases over both closures to have cardinal lambda. Match those bases, extend the coefficient isomorphism to the rational function fields, and then to their algebraic closures K. The resulting automorphism restricts to the prescribed map. This explains why simply citing classification of uncountable closed fields would lose a necessary compatibility. The argument is recorded here for the next worker; the new node itself carries a statement only.

Step 1 uses the statement of the residue-field definition for the two injective field maps and the new large-overfield statement for sigma and its exact bound. Step 2 uses the new conjugacy statement for tau. The additional size inference is the injection k into E. Its bound is checked before conjugacy is applied; no finite-degree assumption enters.

Step 3 uses the existing field-point bijection for j_r and h, residue-field-point-naturality for s j_r and t j_r, Spec functoriality from the affine-spectrum definition, and the fibre-product universal property twice. I opened all four node statements. Each says precisely the fact claimed, including naturality, not merely full faithfulness of a Yoneda embedding. The target projection is Spec(tau), the source projection is the identity. The equations are written in this order to avoid swapping tau and its inverse.

Step 4 uses that same bijection and naturality to compare the two composites with f. The affine-spectrum definition explicitly identifies the unique residue field of Spec K with K. The equations rho alpha_s=id and rho alpha_t=tau then give both inverses by injectivity of rho. This is elementary field algebra, not an assumption that every K-valued point is K-rational. In particular, the image field is proved equal to K using the projection equations.

Step 5 uses the full functor-of-points definition of the groupoid and the fibre-product universal property, both read. The displayed triples and identity/inverse/composition are well typed with the source and target convention of def-a1-groupoid-scheme. Every groupoid law follows in the middle component from the original law and on the outer components by equality. This is a direct restriction construction, not an uncited representability theorem. No proof step exceeds 2000 characters.

I tested the inputs with F finite, F algebraic over its prime field, and F imperfect with an arbitrarily large transcendental overfield. The strict cardinal inequality covers all three; in the equal-embedding case tau can be the identity. Dropping the size hypothesis is invalid: let K be an algebraic closure of Q(t_n : n in N), let F=K, let a be the identity, and extend the shift t_n to t_(n+1) to an embedding b:K into K. Its image is the algebraic closure inside K of Q(t_n : n>=1), which does not contain t_0. Thus b is not surjective and cannot equal an automorphism composed with a. Our argument retains the strong bound and never relies on a small closure of k. For the geometric construction the identity groupoid and the pair groupoid on Spec k give the expected diagonal point; the general argument also allows arbitrary residue extensions and nilpotents in R, because a field-valued point factors through its residue field. I checked the nonalgebraic case specifically to rule out imposing a hidden finite-type hypothesis.

The B-E checklist was applied to the actual files: both new statements introduce every object and define cardinal and prime-field notation inline; their remaining notions name existing definitions; sources give the exact Stacks tag and label; they have empty proof/proof_deps and no embedded proof sketch. The item retains its statement dependencies. Each proof citation has a verbatim entry in citations.json, and proof_deps is exactly the union of uses. The two new inputs neither depend on the item nor repeat its clauses. No statement dispute was found. There is no other worker's review or claimed approval in this report; this is the direct-delivery self-review requested by the brief.

## Unfinished work

The two new field-theory inputs are intentionally statement-only stage-1 queue nodes. There is no unfinished part of this item's one-level split.

## Dry-run repair

The first local duplicate gate rejected a single non-elementary proof step citing both same-tag field inputs. I separated the actual constructions into step 1 (choose the overfield) and step 2 (conjugate the embeddings), retaining their full arguments and the geometric verification in steps 3-5. This is not a relocation of a geometric clause: neither field lemma mentions schemes, and neither alone implies the item. The citations and review numbering were updated.
