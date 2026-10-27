# Stage-1 report: lem-sfb-artin-rs-tangent-tensor

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-artin-rs-tangent-tensor.json`: item, statement unchanged, split into five proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-product-preserving-vector-functor-linearization.json`: statement-only supporting lemma, not in Mathlib after two semantic phrasings, LeanSearch, Loogle and two source searches. One new node, zero Mathlib leaves.
- `citations.json`: one exact statement quotation for every step/node citation.
- `searches.jsonl`: unmodified output log of the required search command; original item search records retained in the item. Sandbox research/write_split.py records the initial construction (the delivered JSON and citations are authoritative).

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for tangent/tensor, Schlessinger, predeformation, linear-functor and product-preservation concepts. The returned ring cotangent and category-theory declarations do not state this deformation-category result. No Lean source was written and no compiler or build tool was run.

## Wanted literature

None. All mathematical source material used is in `literature/stacks-project/formal-defos.tex`.

## Audit and changes

The original item had a statement but no proof. Its statement is correct, including the conditional finite-basis clause and dimension zero. No STATEMENT-DISPUTED correction is needed. Stacks' surrounding base convention assumes a finite map to the residue field, whereas this item has a finite-type field algebra; the direct argument below uses neither finiteness condition, and verifies the test-category objects explicitly. Thus there is no silent application of a stronger base hypothesis.

I read Tags 06IH (lemma-tangent-space-vector-space), 06J7 (lemma-RS-implies-S1-S2), 06I0 (lemma-S1-S2-associated-functor), 06I6 (lemma-linear-functor), 06I8 (lemma-linear-functor-over-field), and 06IA (lemma-tangent-space-functor) in the local TeX. I also read the product comparison immediately preceding 06IA. The recorded proof follows the same square-zero, products, linearization, tensor route as 06IH. Since the item assumes (RS), its stronger groupoid equivalence over the terminal residue groupoid proves the product comparison directly. No separate (S1), (S2), or pi-zero theorem is invoked without a citation: the two-arrow argument is written in step 1. The proof origin is marked agent, reflecting that direct simplification and the explicit basis calculations.

The new lemma is the general input 06I6 specialized to a field. It contains no deformation category, Artinian algebra, tangent space or tensor product, so it neither restates the item nor moves the whole conclusion to another node. Its statement specifies the source category, product comparison, zero value, canonical operations, unique lifted vector structures and linearity on maps. Its proof is empty as required. For future splitting, the source constructs the operations and omits their verification; the standard proof checks each module identity by applying L to the corresponding equality of maps from a finite power, and uses the same diagrams for linearity. This proof explanation is here, not in the new node's statement.

Read the chapter and unit records, the three blueprint levels in SETUP.md, and the latest `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`. This local deformation input descends through the recorded versal-object chain, not a replacement of the unit's direct-image argument. `tools/blueprint_refs.py ancestor` prints `None`; the item has a pre-existing null ancestor and a long via list. I retained those and gave the new node precisely that computed ancestor and the extended via list. No unit realization was edited: this item is not its key node.

## Not duplicates

No existing DAG node carries Tag 06I6 or 06I8. Searches of the whole DAG by those tags, the label lemma-linear-functor and set-valued/product/linearization concepts found no statement supplying the new lemma. Whole-blueprint searches for tangent, Schlessinger, square.zero, 06I6, 06I8, linear-functor and preserves finite products were read.

lem-sfb-product-preserving-vector-functor-linearization vs def-sp-left-exact-additive: the existing node defines additivity and left exactness for functors between abelian categories; it assumes an abelian target and does not construct vector structures on a set-valued functor.

lem-sfb-product-preserving-vector-functor-linearization vs def-weil-linear-functor: the existing definition says what linearity means once both categories are linear; the new statement constructs vector structures from a functor landing in sets. It cites that existing definition.

lem-sfb-product-preserving-vector-functor-linearization vs prop-weil-pbc-rational-transport: the existing blueprint statement transports a coefficient system through scalar localization, not the linearization of a set-valued functor on finite-dimensional vector spaces.

The nodes carrying 06IH/06J7/06I0 (the tangent-ring lifting criterion, Schlessinger hull criterion, proper-scheme deformation hull, this item and its versal-formal-object parent) concern deformation objects or hulls and do not state the generic linearization lemma. They are not used to infer additional clauses from their proofs.

## Review by NS

I checked sections B–E of delivery-errors.md against the JSON and the sources. Each new object and hypothesis is introduced in the statement; the new node has no proof, no proof dependencies and no embedded proof sketch. The only new mathematical source is precisely Stacks Tag 06I6, label lemma-linear-functor, whose field specialization was read in formal-defos.tex. The item uses 06IH's route with direct (RS) gluing and 06I8's actual pure-tensor formula. No SGA source is used.

Step 1 cites def-sfb-artin-deformation-test-category. I opened its full statement: it defines square-zero algebras, covariant groupoid transport, the predeformation terminal residue groupoid and the (RS) equivalence with its triple/arrow description. Exactly these clauses justify the step. I checked the unit inverse in k[V], the finite-dimensional descending-chain argument and the coordinate identification of the algebra fibre product. The augmentation is surjective, so (RS) really applies. The terminal-groupoid hypothesis gives one and only one gluing arrow, making passage to isomorphism classes a product bijection without a hidden theorem about general 2-fibre products. L(0) is a singleton. This is a direct elementary use of the cited definition.

Step 2 cites the new linearization statement and the test-category definition. I checked that L is a functor on all finite-dimensional vector spaces, the product comparison is the projection comparison required by the lemma, and the zero-value hypothesis was established in step 1. The new statement supplies vector structures and linearity both of L(f) and of the map f ↦ L(f), not just functoriality. The existing definition supplies exactly T = F(k[epsilon]). The operations specified in the new lemma identify the deformation addition and scalar multiplication.

Step 3 cites the new lemma and def-weil-pbc-module-tensor-product. The latter's full statement gives the bilinear universal property and generation by pure tensors, which I quoted verbatim. Both are actually needed. The map f_v is linear, depends linearly on v, and L is linear on maps, so the tensor factorization has its full hypotheses. The two inverse calculations are written, using only the basis expansion and bilinearity. No general tensor-representation theorem is smuggled in: the finite-basis argument proves this specialization. I tested r=0, r=1, zero T and infinite-dimensional T with V finite; no finiteness of T is assumed here.

Step 4 uses the same linearity and tensor statements and the square-zero-transport clause of the definition. I checked the naturality equality on x tensor v and its extension by pure-tensor generation. The W=k case is explicitly identified using multiplication, so the final functional evaluations really land in T rather than in an unidentified tensor product. This also covers zero and noninjective linear maps.

Step 5 uses the tensor definition for bilinear evaluation and the established naturality formula. Its finite-basis expansion constructs a functional for every target tangent vector; the statement only assumes a finite basis of T in this conditional clause. For d=0 the zero vector space is a singleton as a set, the zero functional exists, and the image is the entire singleton. There is no missing nonemptiness condition.

All five proof steps are below 2000 characters, with no inline unnamed comparison or hidden standard lemma. I verified that proof_deps is exactly the union of uses, that every citation quote occurs verbatim in its node statement and describes the fact taken from it, and that the item statement is unchanged. The new node is strictly downstream and does not refer back to the item, so it cannot introduce a cycle. The general node's small cases L=constant singleton and L=underlying identity satisfy the statement; the empty constant functor is excluded by L(0)=singleton. Mathlib candidates Free.lift/liftUnique, Functor.Linear and additive_of_preserves_binary_products were opened: each has an already linear/preadditive target hypothesis absent from the set-valued problem. Thus none is an exact or one-line match. Search results were recorded only for queries actually run, preserving their literal query text.

## Unfinished work

No part of this one-level split remains unwritten. The single new statement-only node joins the stage-1 queue. Delivery validation and push results follow the required delivery tool.
