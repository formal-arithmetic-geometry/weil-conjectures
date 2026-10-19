# Worker report

## Files written

- dag/nodes/sec-proetale-coefficients/def-sfb-derived-tensor-hom-adjunction-modules.json: existing definition item, now a Mathlib leaf; no new nodes.
- citations.json: empty list, because a Mathlib leaf has no proof steps.
- report.md: this report. Searches are logged in searches.jsonl by msearch.py.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, derivedTensorHomAdjunction, derivedTensorHom and CondensedRing/derivedHom found only the sheaf-valued counterpart, not the module-object declarations required here. The corresponding exact declarations in /home/ubuntu/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Hom.lean:80,87,94-98 are reference material only: its docstring explicitly identifies the underlying closedness instance as sorried. No master declaration is claimed as a finished attachment.

## WANTED

None. The blueprint and pinned Mathlib sources needed for this item are available locally.

## Corrections and source comparison

The statement is unchanged. The original proof asserted a general closed-category fact with no citation and elementary=null. The general fact is already in Mathlib, so retaining a proof or creating a new generic node would duplicate an existing result. Replaced it with a source-checked Mathlib match covering the parameterized adjunction, its unary specialization and right-adjointness. The imported in_cycle flag is preserved as required; a visited-set traversal of the current statement/proof dependencies found no return path to this item. Historical import flags are not current mathematical claims.

The item has no chapter/unit binding in its JSON and there is no dag/units/sk-def-sfb-derived-tensor-hom.json in this snapshot. Read dag/chapters/sec-proetale-coefficients.json and the actual parent blueprint _section.md instead; no maintainer metadata or unit record was changed. This item is a subordinate clause, not the parent key node.

## Unfinished work

None for this item. The existence of the derived monoidal closed structure is the content of the existing dependencies of def-sfb-derived-hom-modules. This leaf does not claim to construct that structure independently, or to close those dependencies.

## Not duplicates

No new nodes. Whole-blueprint searches were run with tools/blueprint_refs.py search for “tensor hom adjunction”, “adjunction”, and “tensor-hom”, and corresponding DAG searches for closed monoidal categories, internalHomAdjunction₂ and tensor-Hom adjunctions were read. def-sfb-derived-tensor-hom-adjunction-sheaves concerns a different coefficient category; def-sfb-dc-tensor-hom-adjunction concerns a restricted constructible category; sk-def-sfb-derived-tensor-hom contains the current assertion among additional layer-A and tensor-construction assertions. None is a reason to create a node or silently substitute coefficient categories. blueprint.same_as is [].

## Review by N2

I read the current main-20261015 blueprint item .md and .proof.md and its parent sk-def-sfb-derived-tensor-hom/_section.md (Internal hom, Layer B). The source defines RHom as the internal hom of the derived closed structure, rather than as an independently chosen complex-level construction needing a comparison theorem. I opened def-sfb-derived-hom-modules and def-sfb-derived-tensor-modules: the former explicitly says it is the internal hom of the closed monoidal structure on D(Mod_{Λ_X}), and the latter specifies the relative tensor over Λ_X, not tensor over Z. Thus taking this very derived category and its specified monoidal closed structure in Mathlib changes neither the tensor nor the Hom. No boundedness, constructibility, perfectness or finite-coefficient hypothesis is inserted.

There are no retained proof steps to audit under C1/C4: this is a Mathlib leaf. I nevertheless checked every clause against the source code. Clause 1 uses CategoryTheory.MonoidalClosed.internalHomAdjunction₂ in Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:305-307, whose type is exactly curriedTensor C ⊣₂ internalHom. I read the internalHom definition at 290-294, including contravariance in the first variable. Clause 2 is the adj K field of that same object: Mathlib/CategoryTheory/Adjunction/Parametrized.lean:50-58 explicitly makes its type F.obj K ⊣ G.obj (op K). It agrees with ihom.adjunction at Closed/Basic.lean:82-83, with tensor on the LEFT by K. Clause 3 is its right-adjoint witness, already available as the instance at Closed/Basic.lean:296-298; Adjunction.isRightAdjoint is generated as the dual of isLeftAdjoint at Adjunction/Basic.lean:205-206. Each clause is therefore a direct specialization or projection, with no unrecorded mathematical lemma.

I tested K=0 and K=the tensor unit: the former is the zero-to-zero adjunction in the derived abelian category and the latter is the unit adjunction, so neither object is excluded. Empty schemes and the zero condensed ring give degenerate module categories where the same general statement still applies. No nonzero ring, field or characteristic hypothesis is used. The parameter naturality is supplied by the actual ParametrizedAdjunction structure, not inferred just from the existence of unrelated pointwise right adjoints.

For B1-B9 and D1-D5, no new nodes or relabelled clauses were created, all inherited fields and the exact statement were kept, and the match gives the declaration, pinned Mathlib file and read lines for all clauses. The originally unsuccessful unqualified Loogle query is recorded honestly as an unknown-identifier result, followed by the successful fully qualified query; both semantic services worked. All searches in the node came from msearch.py and their hits were inspected. There is no unavailable service or invented search. No SGA route is involved. The only correction was to recognize the existing general Mathlib fact and remove the uncited imported proof. The final dry run is required before handoff; READY will be issued only after deliver.py --no-push prints OK.


## Second reading by N2

- Item statement: checked every hypothesis and clause against the blueprint node and parent Layer B statement; verdict: exact relative tensor over $\Lambda_X$, derived internal hom, parameterized adjunction, and unary right-adjoint clause.
- Mathlib leaf: checked `CategoryTheory.MonoidalClosed.internalHomAdjunction₂` at `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:305-307`, its `adj` projection at `CategoryTheory/Adjunction/Parametrized.lean:54-56`, and right-adjoint instances at `Basic.lean:296-298`; verdict: one-line specialization using the closed structure supplied by `def-sfb-derived-hom-modules`.
- Edge cases: checked $K=0$, the tensor unit, the empty scheme, and zero condensed ring; verdict: no extra nonzero, field, boundedness, or constructibility hypothesis is required.
- No proof steps or new nodes remain: the imported proof is replaced by the verified Mathlib leaf, so there are no uncited step dependencies to audit.

Changes: added the required `mathlib_match.line` (305) for the primary declaration and recorded this second reading; no statement, dependency, or source was changed.
