# Worker report: lem-trf-geometric-inverse-image-exact

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometric-inverse-image-exact.json: statement, split; no exact Mathlib match for the arbitrary geometric-morphism statement, including transported variable-ring modules.
- citations.json: one verbatim statement quotation for each node used in each numbered proof step.
- No new nodes or Mathlib leaves. The existing blueprint ancestry is retained and same_as is empty after the whole-blueprint searches.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint tag, geometric inverse-image exactness, inverseImage exactness and mapCommGrp found no declaration stating this item. The PullbackFlat file uses inverse-image exactness for a different flatness assertion; it is not an attachment. The existing Mathlib leaf lem-weil-pbc-adjunction-lifts-abelian-group-objects already records CategoryTheory.Adjunction.mapCommGrp; no duplicate node was made.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Audit of the imported node and searches

The statement is correct and unchanged. The original source points to exactly the first assertion of Tag 04JC, lemma-flat-pullback-exact. Its second assertion concerns tensor pullback along a flat ring map; this delivery needs only the transported action over the inverse-image ring itself. I read the geometric-morphism definition, chapter record, sk-i-curve-zero unit, and the supplied ancestry: the purpose is underived preservation of the relation cokernel, not an alternative purity or trace route. The item is not the unit's key statement, so no unit record is changed.

The old statement-dependency on sheafification was unused in the statement and removed; sheafification exactness is explicitly cited where its limit description is used in the proof. The exact-functor definition was added as a statement dependency. Existing Mathlib search entries have been retained, and six newly executed queries were appended from searches.jsonl, without inventing any query. The first Loogle pattern had an unknown identifier; its diagnostic is recorded as an invalid query, not evidence of absence. Two LeanFinder phrasings, LeanSearch, and source grep found only partial building blocks, not the combined arbitrary-topos statement. I read Mathlib CategoryTheory/Sites/Pullback.lean:45–75 (a pullback built from a continuous functor), Sites/Sheafification.lean:60–83 (exactness of sheafification), Sites/Abelian.lean:40 (the category is abelian), and Monoidal/CommGrp_.lean:265–300 (the existing adjunction lift). These hits are reused through existing nodes. Whole-DAG searches by Tag 04JC, geometric inverse image, algebraic objects and finite exactness found the cited tools; the site-pullback exactness node assumes a functor of sites and was not silently applied to an arbitrary geometric morphism.

## Tool uses

- lem-weil-pbc-sheaf-algebraic-structures-objects: the generic equivalence between algebraic sheaves and internal algebraic objects is needed for the abelian adjunction lift and to recognize the transported ring. No trace-formula node supplies a replacement.
- lem-weil-pbc-module-sheaves-colimits-forgetful: the generic preservation of limits and colimits by scalar forgetting transfers the abelian result to the variable-ring module category. No trace-formula node supplies a replacement.

These are declared in split_report.tool_uses; no maintainer-owned tool_uses field was set. All other off-unit statement tools are existing Mathlib leaves.

## Not duplicates

No new nodes were created. In particular, the existing adjunction-lift, algebraic-structure equivalence, sectionwise-limits, left-adjoint colimit and scalar-forgetting nodes are cited directly. No clause of this item's conclusion was made into a new node.

## Review by Q51

I read Stacks sites-modules.tex, Tag 04JC (lemma-flat-pullback-exact), including its underlying-set argument and tensor-product second paragraph, then sites.tex, Tag 00YV (proposition-functoriality-algebraic-structures-topoi), its preceding quadruple description and its proof of clause (2). For the module assertion I read Tag 03D2 (lemma-pullback-module), and Tags 03DA–03DB (lemma-abelian and lemma-limits-colimits), including their kernel, cokernel and forgetful descriptions. There are no new nodes requiring further sources.

Step 1 uses the actual finite-limit/adjunction content of def-trf-geometric-morphism. The statement of the existing right-adjoint limit lemma supplies finite products for R, not exactness. The algebraic-sheaves node really states an isomorphism with abelian group objects, compatible with underlying set sheaves. The adjunction-lift node explicitly supplies the underlying functors, structure maps, unit, counit and lifted adjunction. Thus both of its product-preservation hypotheses have been checked. This does not assume that the geometric morphism is given by a continuous functor on the specified sites.

Step 2 uses clause (1) of the sheafification-exactness node, which expressly says abelian-sheaf limits are sectionwise, and the set-sheaf limit node, which explicitly gives the sectionwise criterion. Compatible tuples compute the underlying group limit. I wrote the factorization argument: limit uniqueness proves preservation of addition, zero and negation, so the limiting set-sheaf factor is an abelian-sheaf factor. The algebraic-sheaves node states precisely this operation-preserving criterion. No preservation of cokernels by the set-valued forgetful functor is assumed.

Step 3 uses the adjunction actually supplied in step 1 and the left-adjoint colimit theorem at finite index categories. The enough-injectives node is used only for its explicit assertion that abelian sheaves form an abelian category. The exact-functor definition says preservation of finite limits and finite colimits. The image-as-kernel-of-cokernel argument explains the exact-sequence meaning; the addition formula explains additivity, rather than invoking an uncited additive-functor theorem.

Step 4 is the elementary diagram-transport construction of Tag 03D2, whose published proof consists precisely of applying inverse image to the scalar action through products. The sheaf-of-modules definition makes the action natural, and hence a set-sheaf map. The algebraic-sheaves node recognizes the transported ring. I spell out the action and all kinds of module-axiom diagrams involved. Applying a functor preserves their equations and the finite-product comparisons identify their domains. The abelian adjunction-lift node gives the same transported addition/zero/negation, so the underlying abelian functor comparison is justified on both objects and morphisms. There is no extension of scalars to an unrelated ring.

Step 5 uses the statement of the scalar-forgetting node, which explicitly preserves all limits and colimits and describes kernels and cokernels. It is applicable to both small sites, where abelian sheafification exists. To avoid smuggling in a reflection theorem I wrote the elementary inverse-linearity calculation, and then the canonical finite-limit and finite-colimit comparisons. Their forgotten maps are exactly the isomorphisms already proved in steps 2–3, so reflection of isomorphisms proves the claims in the module categories. Their abelian structure is in the cited sheaf-of-modules definition. All quotations in citations.json were copied verbatim from the corresponding statement fields, and I read those statement fields, not just their proofs or titles.

I checked identity geometric morphisms, the constant-ring case, the zero ring and zero modules, the empty finite diagram, and non-flat changes of rings. For the empty diagram the left exact functor sends the terminal sheaf to the terminal sheaf and the induced abelian functor sends zero to zero; the adjunction handles the initial object. The construction does not assert exactness of tensor extension along a non-flat ring map. There is no noetherian, enough-points, ring-flatness, finite-presentation or special-site hypothesis hidden in the argument. The cited dependency closures do not reach this item. No proof step exceeds 2000 characters. I checked delivery-errors B–E: self-contained existing statement; real logged searches; no new duplicate or clause node; every cited statement actually supplies the fact used; finite index categories satisfy the size hypotheses; all residual diagram arguments are written out. No statement dispute or source error was found.

## What remains unfinished

Nothing in the assigned one-level split. The existing unsplit dependencies retain their own work; no claim is made that the whole closure is proved in Lean. No Lean was written, compiled or built.
