# Worker report — Q81

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-fppf-tensor-model-surjectivity.json`: statement; split into five steps; complete criterion has no one-line Mathlib match.
- `citations.json`: nine entries, one for each step/dependency pair, quoted verbatim from the corresponding statement.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. All non-elementary ingredients already have DAG nodes. The item is not itself a leaf: the tensor equivalence, base-change instance and surjectivity-reflection lemma do not assert the lifted-generator criterion or its full conjunction.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id, tensor-model terminology, fppf, source finite type, and faithfully-flat tensor terminology. No project declaration gives the complete item. The older parent's review mentions a FiniteTypeFppfSourceDescent file, but it is not present in the supplied live Lean source; that review is not attachment evidence.

## WANTED

None. The source used is present locally.

## Findings and changes

The item was statement-only and its statement is correct. No statement, statement dependency, creation history, or imported blueprint field was removed. The Q36 search records were retained; the fresh Q81 searches are appended exactly as logged, including both semantic phrasings. Candidate sources were read at Mathlib/RingTheory/TensorProduct/Maps.lean:476–490, Flat/FaithfullyFlat/Basic.lean:392–397 and :558–566, Descent.lean:40–47 and :63–68, and LinearAlgebra/TensorProduct/Basic.lean:265–271. `cancelBaseChange` and the base-change instance are already represented by the existing leaves. Reflection of surjectivity is written as the direct application of the existing faithful-flatness definition to the three-term complex; it needs no new lemma node.

The latest blueprint (main-20261024, ef6f9619) places the ancestor `lem-a1-affine-hc0` in sk-lem-wrp-hc2 and its proof uses condensed comparisons followed by finite-level support. It no longer spells out the auxiliary schemehood branch recorded in the item's inherited provenance. This delivery retains the assigned chapter/unit and the existing auxiliary branch, and only proves its already-stated 0367 ring input. It does not edit or propose an alternative to the unit or chapter route.

## Not duplicates

No new node pairs: no new nodes were created. Whole-DAG searches found `lem-weil-pbc-tensor-cancel-base-change` and `lem-weil-pbc-faithfully-flat-base-change`, both Mathlib leaves, which are reused. The full-DAG search by `surjective_of_tensorProduct`, `codescendsAlong_surjective`, `lTensor_surjective_iff_surjective`, and by faithfully-flat reflection/exactness wording found a local-ring special case, `lem-pc-local-flat-faithful-flat-reflects-surjective`; it is not applicable because this item assumes no local rings. The general exactness equivalence is already the statement of `def-weil-pbc-faithfully-flat-ring-map`. Whole-blueprint searches by the model criterion, tensor and faithfully-flat wording found no blueprint node stating this entire conjunction; `same_as` remains empty.

## Review by Q81

I read descent.tex, Tag 0367, `lemma-finite-type-local-source-fppf-algebra`, the full statement and proof at lines 4351–4381. The present item isolates the final argument after the finitely presented model has already been supplied. Its hypothesis that e is the induced A-algebra isomorphism is essential: an arbitrary abstract ring isomorphism would not give the map comparison. I checked this hypothesis and the commuting C-maps, and kept the given formulas. I also read algebra.tex, Tag 00HB, `definition-flat`, items 2 and 4: it explicitly reflects exactness of complexes, which supplies exactly the reflection used here. No finite-presentation or Noetherian hypothesis enters any of the five steps. No SGA source is used.

Step 1 cites `lem-weil-pbc-algebra-tensor-pushout-universal-property`, whose statement actually constructs the induced map from compatible ring maps and specifies its values on pure tensors; it is not merely a definition of a pushout. The C-composites agree by the item's hypothesis. Evaluating on r_P tensor 1 proves the R-compatibility needed for polynomial evaluation. The generating interpretation is literally in `def-weil-pbc-finite-type-algebra`; evaluating F at the z_j gives a preimage of every b. This is an elementary evaluation argument, and no generator-surjectivity lemma is hidden.

Step 2 uses the statement of `lem-weil-pbc-faithfully-flat-base-change`, with C as its base, D as its faithfully flat algebra, and P as its arbitrary base extension. Its displayed map is precisely p to p tensor 1. The map C to P is present without requiring any map R to C. This is the only permanence result used.

Step 3 reads the complete statement of `lem-weil-pbc-tensor-cancel-base-change`: it gives an A-algebra equivalence, both the forward formula and the inverse formula. Substitution C to P and P to A yields exactly c, and composition with the given e yields theta. The remaining equality theta(1 tensor z)=q(z) is proved first on p tensor d and then by additive/C-linear extension; `def-weil-pbc-module-tensor-product` explicitly says pure tensors generate the module. Thus the step identifies the actual base-change map, rather than just exhibiting an isomorphic ring. It has 682 characters and hides no comparison lemma.

Step 4 uses only the statements of the tensor definition, natural module tensor commutation, and faithful-flatness definition. The map lambda is the map induced by phi and the identity, and e lambda=q is checked on pure tensors. Bijectivity of e and surjectivity of q give surjectivity of lambda. The statement of `lem-weil-pbc-module-tensor-comm` includes naturality, so it gives exactly the swap conjugation to id_D tensor phi, with no appeal to its proof. The complex P to A to 0 consists of C-linear maps and has composite zero; A's C-action is through phi by hypothesis. After tensoring with D, surjectivity is equivalent to exactness in the middle; D tensor 0 is zero because its generators are zero. The reflection of exactness is literally the clause of `def-weil-pbc-faithfully-flat-ring-map` quoted in citations.json. This is an elementary instance of that definition, not a general unproved descent theorem. In particular, flatness alone is never used to infer reflection. The step is 790 characters and does not conceal a separate lemma.

Step 5 takes an arbitrary a, chooses its preimage p using the surjectivity just proved, and evaluates a polynomial expression for p in the specified p_i. The same finite-type definition states that polynomial interpretation. This proves the specified generator family, rather than merely existence of some generators.

I checked the boundary cases. When n=0, every b comes from a constant polynomial over R, and step 1 still supplies its preimage through R to P; no z_j is selected. When N=0 the same argument with constant polynomials proves the last clause. If D=0, faithful flatness forces C=0 (apply exactness reflection to 0 to C to 0); the unital maps from C force P,A and B to be zero, so the formulas and conclusions remain valid. B=0 with C and D nonzero is also allowed when A=0; q and phi are then maps to the zero ring and are surjective. When C=D with the identity map, Q=P and cancellation reduces to the usual tensor unit identification; the generator argument still proves the conclusion. No nontriviality or positive generator count was silently imposed.

I checked delivery-errors B–E against the actual node statements. There are no new statement-only nodes to conceal an argument or duplicate a clause; the five steps carry the whole proof. Non-elementary tensor cancellation and faithful-flat base change cite their existing nodes. All nine dependency citations are covered by verbatim quotes, proof_deps is their union, and none of these dependencies depends on the item. The chapter/unit records were read and left unchanged; the cited statements from other units are Mathlib tools or definitions, so no unit route is substituted. The existing module commutation node contains doubled TeX backslashes in its own statement; it is cited verbatim and is outside this delivery's edit scope. The item's new text uses single TeX backslashes. There was no returned delivery to repair. The only corrections while drafting were to make the R-map check, tensor swap, exactness reflection, and zero-tensor argument explicit.

## Unfinished work

None. The required server dry run exited successfully with OK (not pushed) at c45df5215a5; preflight passed. This report update is checked by a final dry run before direct delivery.
