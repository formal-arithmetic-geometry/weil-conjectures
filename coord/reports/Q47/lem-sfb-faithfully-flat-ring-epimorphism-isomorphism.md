# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-faithfully-flat-ring-epimorphism-isomorphism.json`: existing statement, now split into three elementary steps. Mathlib searches find ingredients but no exact declaration or one-line specialization that supplies all hypotheses and the conclusion.
- `citations.json`: five records, one for each use in each step, with verbatim statements of the cited nodes.
- `report.md`: this report. `searches.jsonl` was produced by the mandatory search command.

New nodes: 0. New Mathlib leaves: 0. All proof dependencies already exist and are Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, faithfully-flat ring epimorphisms, and the categorical candidate names. No project declaration gives this conclusion. Source declarations concerning faithfully flat descent or Amitsur exactness are not exact attachments. No Lean was written and no compiler or build was run.

## WANTED

None. The source needed for this proof is present in `literature/stacks-project/algebra.tex`.

## Problems found and changes

The existing statement is correct, including its explicit absence of finiteness hypotheses. Its proof was empty. Stacks 04VU, `lemma-faithfully-flat-epimorphism`, invokes the tensor criterion in `lemma-epimorphism` (whose proof is omitted) and leaves the faithful-flat descent inference implicit. I expanded both: epimorphy equates the tensor inclusions; multiplication is the inverse by a pure-tensor calculation; the tensor of f identifies explicitly with this inclusion and exactness reflection applies to two three-term complexes.

I preserved the statement, statement dependencies, inherited searches, source, created record, chapter and unit. Added only the completed proof, dependency union, current logged searches and split report. The existing candidate list remains useful for later formalization, but no candidate is asserted to prove the item directly.

`tools/blueprint_refs.py ancestor` returns a null ancestor for this inherited created node. Its inherited `blueprint.from.node = null` and long via chain are retained rather than inventing a blueprint ancestor. Its from.place already specifies 04VU in the 04VV/03DP direct-image ancestry. Searches of all imported blueprint nodes for faithfully flat and epimorphism and of the latest blueprint text found no same statement; same_as is empty. The unit record is not this item's statement, so no realized fields are changed. This elementary ring calculation supports the existing downstream route; it does not replace a step of the unit.

## Not duplicates

No new nodes were created. Whole-DAG searches by 04VU, faithfully-flat epimorphism, tensor descent, categorical regular monomorphisms and the candidate declarations were read. In particular I reused the existing algebra-tensor pushout and module-tensor definitions. I did not create separate nodes for equality of the inclusions, for the multiplication inverse, for the tensor unit identification, or for faithful-flat bijectivity reflection: all are written explicitly as short consequences of the cited statements and definition. The larger Amitsur exactness node and universally injective ring-map node are unnecessary here.

## Review by Q47

I read Stacks `algebra.tex` at `lemma-faithfully-flat-epimorphism` (04VU), `lemma-epimorphism` and its four equivalent assertions, `definition-flat` (00HB), and `lemma-tensor-product` (00CX) with the pure-tensor generation in its proof. This is exactly the source's tensor-and-descent route. No SGA source is used. There are no new nodes requiring additional source review.

For step 1 I opened `lem-weil-pbc-algebra-tensor-pushout-universal-property` and checked that clause (1) actually supplies a commutative tensor ring and the two unital R-algebra inclusions. Their composites with f agree by their R-algebra property (or by tensor balancing). Thus the hypothesis applies to the actual commutative ring B = S tensor_R S and gives equality of those two maps. This does not confuse a ring epimorphism with a surjective map. This step is elementary, a direct use of the given cancellation hypothesis.

For step 2 I checked clause (2) of that same node with C = S and both maps the identity: it supplies the multiplication homomorphism and its formula on all pure tensors. Clause (1) supplies multiplication of pure tensors. I separately opened `def-weil-pbc-module-tensor-product`, whose statement explicitly says pure tensors generate. Both compositions with the inclusion are then computed, including the crucial use of equality of the two inclusions. Therefore the assertion that the inclusion is an isomorphism is proved here, not borrowed from a missing tensor-epimorphism lemma. This is a short elementary inverse calculation, not a restated clause delegated to a new node.

For step 3 I reread the module tensor definition and its universal property. The bilinear formula u(s,r) = s f(r) gives the tensor unit map. Its inverse is checked with the balancing relation s f(r) tensor 1 = s tensor r. The map S tensor f has formula s tensor r maps to s tensor f(r); the equality to i_1 u is checked on generators. Thus it really is the scalar extension of f, not an unrelated isomorphism. Tensoring the zero module gives zero from bilinearity and generation. Finally I opened `def-weil-pbc-faithfully-flat-ring-map`: it states exactly that every three-term complex is exact if and only if its tensor with S is exact. Applying it to 0 -> R -> S reflects injectivity, and applying it to R -> S -> 0 reflects surjectivity. Both are complexes because the other arrow is zero. No unnamed theorem on descent, preservation of cokernels, or detection of zero objects is needed. The final inverse-ring-map observation follows by injectivity and the ring homomorphism axioms. The elementary marking records these explicit applications of the definition; it does not label a hidden descent theorem elementary.

I checked the C4 quotes against the statements, and every cited fact is supplied by those statements. For C1, the only results invoked besides the hypothesis are the cited tensor universal properties/ring structure and the exactness-reflection definition; the inverse and unit calculations are given rather than hidden. No source tag is used as a replacement for a missing node. Every uses id exists, the proof_deps list is their exact union, and all dependencies are established Mathlib leaves, so no new cycle or off-unit theorem route is introduced.

The small cases check the missing-hypothesis risks. If S is the zero ring, faithful exactness reflection forces R to be zero (or step 3 proves f injective), so the argument still applies. If R is zero, a unital map forces S to be zero. The identity map, including on the zero ring, satisfies every calculation. The localization Z -> Q is a ring epimorphism and flat but fails faithful flatness: (Z/2) tensor_Z Q is zero, and the reflection step is unavailable. The faithfully flat diagonal k -> k x k is not a ring epimorphism: the two projections to k agree on k but differ, so step 1 fails exactly where it should. No nonzero-ring, finite-module, finite-type, finite-presentation or field hypothesis has been inserted.

I read delivery-errors B--E point by point. There is no new node with missing hypotheses, duplicate content, unnamed notions, unrun searches, proof text in a statement-only node, or unverified Mathlib match. The item keeps its original statement. The proof has no circular citation or relabelled subclauses and expands the source's omitted argument. Each step is below 2000 characters; there is no long step hiding a separate lemma.

The six current Mathlib searches are precisely those logged by msearch.py: two semantic phrasings through LeanFinder, one Loogle query, two greps, and one LeanSearch query. I read the hits and the source of `Module.FaithfullyFlat.bijective_of_tensorProduct` (Descent.lean:49), `CommRingCat.epi_iff_epi` (Epi.lean:26), the finite epi criterion (Epi.lean:46), the regular-mono construction (EqualizerPushout.lean:64), and the tensor characterization (Algebra/Algebra/Epi.lean:37). The descent theorem needs the explicit tensor-bijectivity argument; the finite criterion needs an absent hypothesis; the categorical route needs two separate theorems. These are ingredients, not an exact attachment or single one-line specialization of a declaration for the item.

## Unfinished work

None in the mathematical split. Delivery verification is performed with the required server dry run and then the push command.
