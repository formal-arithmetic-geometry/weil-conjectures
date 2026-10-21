# Q58: lem-sp-proetale-direct-image-scalar-cocycle

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-proetale-direct-image-scalar-cocycle.json`: item, statement unchanged, five proof steps, status split. No exact Mathlib match.
- `citations.json`: twelve verbatim statement excerpts, one for each node used by each step.
- `report.md`: this report.

No new nodes or Mathlib leaves. `prepare.py` is sandbox-only preparation code; `searches.jsonl` is the search command's log.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and the direct-image scalar comparison names, and for mate, coefficient and scalar-cocycle terminology. The generic mate-pasting proofs and `AlgebraicGeometry.ProEtale.fieldExtendScalarsCompIso_cocycle` do not state this theorem: the latter concerns successive finite extensions of rational coefficient fields and scalar associators, without this direct-image counit mate. The published `lean/Sheaf/SecSmoothPurity/DirectImageScalarOperations.lean` defines the actual comparisons, and `DirectImageScalarExchange.lean` concerns geometric-square exchange; neither is an eligible upstream attachment for this item.

## WANTED

None. All sources used are in the read repository.

## Findings and changes

The imported item was an unsplit, correct ambient natural-transformation identity. It has no Lean audit or declaration claiming a finished proof. Its source is Step 4 of the current blueprint direct-image proof, which says the counit transposes compose without writing that calculation. The main-20261015 chapter and coefficient-comparison unit were read; this work realizes the unit's coefficient-composition sentence and does not replace its compactification or finite-window route for proving invertibility.

A whole-DAG concept search, including the 0G7E/06YS/0037 source tags, located the already split `lem-pur-ringed-coefficient-projection-cocycle`. Its statement supplies exactly the more general coefficient-change cocycle, for arbitrary sheaves of rings and ordinary unbounded module derived categories. Reusing that theorem avoids introducing a second version of it or a separate new node for one of the item's clauses. The task is therefore a specialization with its normalization checks written out. The item itself is retained and split, since it records the designated pro-etale constructions used by its parent.

The statement, four statement dependencies, source, creation record and blueprint ancestry were preserved. The proof now checks the actual coefficient-ring maps, target coefficient actions, balanced associator, geometric adjunction and counit transpose, then applies the general cocycle. Generic off-unit statements are declared in `split_report.tool_uses`. The proof is marked agent-written: it makes the explicit specialization using existing theorem statements and the Stacks constructions, rather than claiming that Stacks prints this particular pro-etale formula.

The whole-blueprint searches were `scalar cocycle`, `pullback tensor`, `direct image coefficient`, `counit scalar`, `coefficient associativity`, `projection cocycle`, and `coefficient projection`. The hits either give broader operation packages, unrelated field-extension associators, or the parent comparison. None is another blueprint statement of this exact ambient identity. The nearest blueprint ancestor was checked with `blueprint_refs.py ancestor`; it is `det-sp-reduction-direct-image`.

The five searches newly logged for this item used LeanFinder twice with different formulations, Loogle, LeanSearch, and Mathlib grep. Read their returned hits, and inspected `Mathlib/CategoryTheory/Adjunction/Mates.lean:170` and `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:984` and the ensuing scalar-unit formulas. `mateEquiv_vcomp` is a general pasting theorem; `ModuleCat.extendScalarsComp` is ordinary-module associativity. Neither alone identifies the canonical derived coefficient maps in the item, so the item is not a Mathlib leaf. The older search records were retained; all new records correspond exactly to the command log.

## Not duplicates

No new nodes were created. The existing general `lem-pur-ringed-coefficient-projection-cocycle` is cited, not cloned. The auxiliary scalar-associativity fact is reused from `lem-sfb-successive-derived-quotient-normalization`; no new associativity, pullback-coherence, mate-pasting or finite-ring specialization node is introduced.

## Review by Q58

I read the item's current blueprint source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md`, especially Step 4, and the scalar-extension proof paragraph (4). I also read the local Stacks text: sites-cohomology.tex, Tags 06YS (`lemma-K-flat-resolution`), 0G7E (`lemma-pullback-K-flat`), 06YY (`lemma-derived-base-change`), 0D6D (`lemma-derived-pullback-composition`), 07A4 (`lemma-pullback-tensor-product`), 07A6 (`lemma-adjoint`), 07A7 (`remark-base-change`) and 0E47 (`remark-compose-base-change-horizontal`); categories.tex, Tag 0037 (`definition-adjoint`) and the equivalent counit description immediately following it. The Stacks horizontal-composition remark explicitly omits its verification; the existing general cocycle node, rather than an uncited assertion that composition is standard, is the theorem used for that part. There are no new nodes needing separate sources.

For step 1 I opened the statements of `def-weil-pbc-proetale-operations`, `lem-pur-proetale-constant-coefficient-comparison`, and `def-weil-proetale-inverse-image`. The first specifies the ordinary unbounded operations and their adjunction, the second proves that the actual constant-coefficient structure map is an isomorphism for every scheme morphism, and the third defines its constant-section adjunct and scalar action. Thus replacing inverse-image coefficient rings by the named constant rings uses exactly the canonical maps. For each of the two coefficient maps I checked the square on constant sections, then on their local restrictions and gluing; no coefficient flatness, or invertibility of ell on a scheme, is used.

For step 2 I read the full statements of `lem-pc-kflat-resolution`, `lem-sfb-successive-derived-quotient-normalization` and `det-sp-scalar-extension-functor`. The resolution node gives flat terms as well as K-flatness; the normalization node explicitly gives the double-tensor formula, its inverse and its validity in the unbounded categories for arbitrary sheaf ring maps. This is precisely the associator used in the scalar-extension definition and in its source paragraph (4). I checked the direction (iterated to direct), the factor psi(b)c rather than an untyped product of b and c, and the C-action on the right factor. I did not deduce K-flat preservation or derived tensor associativity from a definition of flatness.

For step 3 I read `def-sp-reduction-direct-image-comparison`, the general cocycle statement, `def-weil-pbc-proetale-operations` and `lem-weil-pbc-adjunct-counit-identity`. The comparison definition explicitly specifies the balanced K-flat pullback isomorphism and its counit transpose. The general cocycle defines chi by the identical transpose, with the same normalized geometric adjunction after step 1's coefficient identifications. The adjunct-counit node states the equivalence used to identify those morphisms uniquely. In particular I checked equality of the specified gamma maps; an arbitrary isomorphism of pullback functors or of adjunction data would not suffice.

For step 4 the only cited statement is `lem-pur-ringed-coefficient-projection-cocycle`, which contains the displayed chi/tau equality verbatim. Its small-site, inverse-image-ring and ordinary-derived-category hypotheses are established in step 1. Steps 2 and 3 identify every symbol that is substituted. I checked the two morphisms' common source and target in D(Y,C), including which object is passed to the B-to-C mate. This is a generic theorem of another unit, used as a tool and declared as such; it does not replace a geometric or purity step in the unit's route. I checked its transitive dependencies do not reach the present item.

For step 5 the same general node says the equation is an identity of natural transformations and explicitly imposes no flatness or invertibility of chi. Its hypotheses permit an arbitrary geometric morphism and arbitrary unbounded objects. Hence naturality in E and all the absence-of-extra-hypothesis clauses really follow from its statement, rather than its proof or a bounded constructible variant.

I checked delivery-errors B through E against these files. There are no new statements, hollow definitions, new clause nodes, missing new-node searches, or statement changes. Every node cited in a step was opened and its statement checked; each citation has a literal excerpt in `citations.json`. The non-elementary ingredients are the cited existing comparison, resolution, associativity and cocycle results, not uncited source tags. All five proof steps are under 1200 characters, and none hides a new standalone lemma.

As edge cases I checked E=0, the identity scheme map, identity coefficient maps, a zero target coefficient ring, and empty schemes. The formula then reduces respectively to the zero equality, scalar associativity with the identity geometric mate, the scalar unitor, or the unique morphism in the zero derived category. For the nonflat tower Z/ell^2 -> Z/ell -> Z/ell, the proof still uses the flat-term K-flat normalization theorem; it never assumes a finite projective resolution of the middle ring. Properness is not used even for a nonproper structural scheme map, and no cohomological bound or constructibility assertion enters the argument.

The first dry run requested longer excerpts for the two operations-node citations; I expanded each to the complete concluding operations-and-adjunction paragraph. This changes only the citation evidence, not the proof.

The second dry run flagged two uses of the phrase “the item's” in proof prose under its self-containedness rule. I replaced them with “the prescribed operations” and “the specified mate”; all objects were already introduced in the statement and preceding steps.

## Unfinished work

None for this stage-1 split. The independent maintainer review remains the project's normal review step. No Lean files were written and no compiler, Lake or build tool was run.
