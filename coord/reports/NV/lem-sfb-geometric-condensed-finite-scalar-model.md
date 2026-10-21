## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-geometric-condensed-finite-scalar-model.json: item, split, statement unchanged; Mathlib searches found no exact declaration.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-action-derived-section-transport.json: statement-only tool, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-supported-lattice-norm-projection.json: statement-only geometric generator lemma, unsplit, no Mathlib match.
- citations.json: full verbatim cited statements for every step/node pair.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and geometric/condensed/scalar-model terminology. The additive curve scalar-model declarations concern a different coefficient problem and do not state this item. Mathlib search hits about condensed constructors, light condensed monoidal categories, algebraic field scalar towers and Galois groups do not state these comparisons.

## Wanted literature

WANTED: an exact source for the ordinary derived all-continuous norm-topology projection on a supported rationalized lisse integral lattice over a separably closed positive-characteristic field, for lem-sfb-supported-lattice-norm-projection. The blueprint paragraph (3) provides the route, not this statement or a proof. No completion or solidification is implicit.

WANTED: a combined reference for coefficient-normalized ordinary unbounded field/action derived section transport, including forgetting the action and finite-dimensional norm representations, for lem-sfb-field-action-derived-section-transport. Bhatt–Scholze Example 4.1.10 gives the field site and Definition 6.8.3 / Proposition 6.8.4 give the finite-field lisse convention; the new normalization package is agent-formulated rather than quoted as a theorem of that paper.

## Corrections and route

No statement correction or STATEMENT-DISPUTED claim is made. The requested finite scalar model must retain its continuous Galois action: forgetting G is conservative for detecting isomorphisms, but taking arithmetic invariants would introduce cohomology that need not be bounded. The proof therefore never infers bounded arithmetic cohomology.

The tempting existing lem-sfb-continuous-algcl-proper-scalar-comparison and lem-sfb-continuous-algcl-open-scalar-comparison were rejected as proof inputs: their dependency path passes through lem-sfb-constructible-algcl-topology-comparison, lem-sfb-supported-finite-stage-topology-defect, lem-sfb-norm-algcl-cohomology-topology-comparison and back to this item. A dependency graph search checked this explicitly. The rational direct-image theorem, finite-subextension direct-image comparison and lattice generators do not have that path.

Read the current blueprint direct-images proof paragraph (3), its whole chapter description, the sk-thm-sf-ctf-stability unit record and SETUP's three levels. The item's inherited blueprint.from.node is null; blueprint_refs.py ancestor also prints None. Its existing place is already specific and the via chain is preserved. Blueprint searches for geometric cohomology, condensed finite, geometric section, supported lisse, rationalized lattice, action modules, field equivalence and field site found no identical blueprint statement. The item is not the key statement of its unit, so no realized fields are changed.

The field/action transport tool isolates descent and coefficient normalization, with no geometric finiteness or projection-isomorphism conclusion. The norm lemma is restricted to a single supported rationalized lattice over a separably closed field; it has no arbitrary constructible input, arithmetic action or coefficient-square conclusion. Finite generation and triangulated induction in the item genuinely extend that restricted input. Neither new node simply restates a clause of the item. The hard incomplete norm-coefficient analytic input remains visible as an unsplit node instead of being claimed from the wrong topology in HRS.

## Not duplicates

lem-sfb-field-action-derived-section-transport vs lem-sfb-field-profinite-galois-site: the latter states a dense site equivalence on qcqs field objects; it does not state the module derived transport, coefficient-adjunction normalization, forgetting-of-action comparison, or finite-dimensional representation realization.

lem-sfb-field-action-derived-section-transport vs lem-sfb-condensed-galois-global-descent: the latter's statement gives derived global sections as derived invariants, not a field module equivalence or the comparison before taking invariants. I read its proof as a guide to a prospective proof of the new input, but the item cites only the new input for that stronger interface.

lem-sfb-supported-lattice-norm-projection vs lem-sfb-qlbar-direct-image-comparison: the existing result uses finite-subextension-valued C, not all norm-continuous B.

lem-sfb-supported-lattice-norm-projection vs lem-sfb-continuous-algcl-proper-scalar-comparison: that node treats proper maps and depends transitively on this item. The new input treats geometric sections of one supported rationalized lattice and makes no proper relative comparison assertion.

lem-sfb-supported-lattice-norm-projection vs lem-sfb-lattice-supported-hom-finite-comparison: that node gives finite quotient reductions and derived Hom identifications, not all-continuous norm-coefficient geometric sections.

lem-sfb-supported-lattice-norm-projection vs det-lem-integral-models-generators: the existing statement provides a finite construction from generators and their finite reductions, not scalar projection for those generators.

No new source carries a Stacks tag. No same-tag duplicate pairs are hidden. Any Stacks sources already attached to reused general tools retain their existing tag/label data; no new Stacks attribution is invented for an analytic input.

## Review by NV

I read delivery-errors B–E in full, then compared each cited node's actual statement with the assertion taken from it. New nodes have only statements, empty proof/proof_deps and explicit independently introduced objects. They define their parameter tests, coefficients, actions, projection maps and topology; their statement dependencies name the corresponding definitions. The two new source places explicitly distinguish source material from agent-formulated missing interfaces. I read Bhatt–Scholze Example 4.1.10, Definition 6.8.3, Proposition 6.8.4 and Remark 6.8.15 in the local PDF text, and HRS Lemmas 5.6 and 7.9 with their topology discussion. HRS explicitly equips Qbar with the colimit topology; I did not use it to assert the norm-topology projection.

Step 1 uses exactly the new field/action transport statement for the module equivalence, derived section identification, actual scalar units/counits and conservative forgetful functor. The existing Galois descent node alone would not supply this interface, so the new tool exposes it as a separate obligation. In step 2, lem-sfb-dc-lower-star-preserves explicitly includes finite E and arbitrary positive-characteristic base fields with ell invertible. Its hypotheses hold for X -> Spec k. The constructibility definition uses finitely presented scalar E-modules, which are finite-dimensional and free; on Spec k every nonempty stratum is the point. Thus the finite-dimensional representation clause of the new field tool applies to each homology module. The bound is retained by its t-exact equivalence; no finite cohomological dimension of k is used.

Step 3 takes the actual counit-normalized coefficient projection from lem-sfb-qlbar-direct-image-comparison, whose statement allows qcqs morphisms and bounded-below complexes. V is bounded, and the separated finite-type hypothesis gives qcqs by the cited qcqs-over-affine statement. This is specifically the C coefficient. The field tool then transports the same map. In step 4, exact pullback and constructible pullback are supplied separately by their cited statements; neither is being assumed from a definition. Base change gives a separated finite-type k^s-scheme with the same distinct p and ell. det-lem-integral-models-generators(1) actually asserts finite cones and shifts from supported rationalized O_E-lattices over that fixed E, which is exactly the induction used.

Step 5 applies the new norm projection statement only to those generators over the separably closed field k^s. lem-sfb-ringed-projection-first-shift supplies exactness and shift/connecting compatibility in the input variable; triangle-two-out-of-three supplies the cone step. This gives the argument for the full constructible input, and the cited transport statement detects the equivariant isomorphism from its forgotten map. It does not assume tensor commutes with arbitrary limits or infinite totalizations. Step 6 uses the coefficient-projection-cocycle statement, which explicitly concerns ordinary derived categories with no flatness condition and gives compatibility of the canonical maps. Taking the scalar-adjunction transpose of both paths reduces them to the same v -> 1 tensor v, and c(1)=1; the new field tool preserves these units, so the equality is the square requested in D(A_G(C)), before restriction to A. Step 7 cites the stated natural and shift structures, including third arrows, rather than claiming an unspecified isomorphism is compatible.

I tested the item and both new statements on the empty scheme/support, rank zero, V=0, G=1, X=Spec k and coefficient-unit maps. At a separably closed point the norm lemma becomes B tensor_A A^r -> B^r, so no spurious completeness or finite-subfield-valued condition appears. The field tool permits arbitrary condensed rings but its finite representation assertion is restricted to finite normed E, not to C or B. Scalar extension need not be exact on ambient condensed modules anywhere in the new norm input or the item: all such tensors are derived. The inherited item statement and its C/B distinction remain unchanged.

Every non-elementary proof step is below 2000 characters, and I checked that no long step hides a separate lemma. The analytic generator input and the field/derived descent transport are explicitly named nodes, rather than suppressed with “standard” or “transport.” citations.json contains the actual statements verbatim, one entry for every use. All recorded new-node searches came from the required msearch command and their returned hits were read; two different semantic phrasings were tried for each new node. No Lean was written, no compiler or Lake was run, and all writes are in this sandbox.

## Unfinished work

The item is split by one level. The two new unsplit inputs require their own future proofs and exact literature references; this is recorded, not treated as established Lean. No item clause or delivery check is intentionally left unfinished.
