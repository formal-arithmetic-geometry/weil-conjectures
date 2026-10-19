# Stage-1 report: def-sfb-finitely-presented-module

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-finitely-presented-module.json`: existing definition, split; no exact Mathlib match. Four existing statement dependencies identify the ambient abelian-category structure, ring object, module category and regular module, and the theorem supplying abelianness of that module category.
- `citations.json`: empty list, because this definition has no theorem proof steps.
- `searches.jsonl`: records produced by the required msearch command; all queries were actually run and their results read.
- `report.md`: this handoff. No new nodes, no new Mathlib leaves.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, `IsFinitelyPresented`, and finitely-presented terminology found no project declaration of this internal-module predicate. Ordinary algebraic finite presentation elsewhere in that tree is a different kind of object.

The reference master has `CategoryTheory.Mod.free` and `CategoryTheory.Mod.IsFinitelyPresented` in `WeilConjectures/CategoryTheory/ModuleObjects/Free.lean`, lines 38 and 48. I read the entire file: it uses finite biproducts of the regular module and an existential isomorphism with a categorical cokernel, exactly the intended predicate. This is reference material on the wrong branch, not a finished-proof attachment, and I have not recorded it as closed.

## WANTED

None. The current blueprint definition, its surrounding unit/chapter text, the module-object definition and the abelianness lemma were available locally. No Stacks theorem is needed to introduce this predicate; the definition's source is the blueprint, not an invented Stacks attribution.

## Problems found and changes

The imported definition cited `sk-prop-sfb-module-category`, which is a current blueprint proposition but has no corresponding DAG node file. Its abelian-structure clause is stated by the existing node `lem-sfb-modobj-abelian`. I replaced the dangling citation with that node rather than creating a duplicate or citing a nonexistent object. The imported `stmt_deps` contained only `sk-def-sfb-module-objects`; I added the other three dependencies actually used in the rewritten definition.

The defining property and hypotheses are unchanged: the tensor product is additive in each variable; the ring object need not be commutative; tensoring on the left by R is right exact; the ranks are natural numbers; and the isomorphism and cokernel live in the module category. I expanded the meanings of right exactness (finite-colimit preservation), finite biproduct, the zero rank and cokernel so the statement can be read without depending on unnamed conventions. This is a definitional clarification, not a statement dispute or replacement by filtered-colimit compactness. No theorem has been inserted into the definition without a named source: module-category abelianness is delegated to the existing lemma.

The newly imported item has no `chapter` or `unit` fields, and this snapshot has no `dag/chapters/sec-proetale-coefficients.json` or `dag/units/sk-def-sfb-constructible.json`. I read the corresponding current blueprint `_section.md` files directly and preserved the base metadata. This item is a subordinate definition, not the statement of its surrounding constructibility unit, so no unit realization is changed.

## Unfinished work

None for this one-level stage-1 definition split. The existing internal-module and abelianness nodes remain their own items. No Lean was written or compiled; no git command was run by the worker. The authorized delivery tool performs its own isolated worktree operations.

## Duplicate search and Mathlib verdict

I searched the entire imported blueprint with `tools/blueprint_refs.py search` for `finitely presented`, `finite presentation`, `biproduct`, and `cokernel`, and searched `dag/nodes` for the corresponding terminology. `pur713-def-finite-presentation` is the analogous exact-sequence definition only for a commutative ring object in pro-etale abelian sheaves. It does not replace this definition for possibly noncommutative monoid objects in arbitrary abelian monoidal categories. Local finite presentation and finite constant local models also impose geometric or scalar-ring conditions not present here. No equivalent second general statement was found, so `blueprint.same_as` is empty. There are no new nodes requiring a same-tag pair comparison.

The actual msearch calls used two semantic phrasings, two Loogle name patterns, LeanSearch, and source greps. I read `Module.FinitePresentation` in Mathlib/Algebra/Module/FinitePresentation.lean:61-67, `CategoryTheory.IsFinitelyPresentable` in Mathlib/CategoryTheory/Presentable/Finite.lean:49-74, and `CategoryTheory.Mod` and `Mod.regular` in Mathlib/CategoryTheory/Monoidal/Mod.lean:215-240 and 330-350. The first predicate concerns type-valued modules; the second concerns preservation of filtered colimits by Hom. Neither states the existential finite-regular-module cokernel predicate for this general ambient category. The generic internal-module notions are present, but their file has no such predicate. A mistaken early grep used the nonexistent directory `CategoryTheory/Monoidal/Mod`; its zero hits are explicitly marked inconclusive, and I reran the search on the real Monoidal directory and its actual Mod.lean file. All of these results, including that mistake, are recorded honestly in the item.

## Review by Q67

I read the complete current source `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/def-sfb-finitely-presented-module.md`, its constructibility unit and chapter, and the reference master's Free.lean. The latter confirms that m and n range over natural numbers and that the cokernel and isomorphism are internal to `Mod C R`. I did not substitute ordinary modules or assume commutativity, a tensor unit that is a generator, compactness of that unit, closedness, or the Grothendieck property. None is a hypothesis of this definition.

There are no proof steps to audit under C1/C4: this item is a definition. Instead I checked every statement dependency against its actual statement. `sk-def-sfb-ring-object` defines a monoid object, including multiplication and unit. `sk-def-sfb-module-objects`, clauses 1 and 2, defines left module objects and their morphisms and explicitly states that the regular module is R with multiplication as action. I use exactly that clause, not a consequence of its proof. `lem-sfb-modobj-abelian` assumes an abelian monoidal category, additivity in both variables and preservation of finite colimits by R tensor -, and concludes that the internal module category is abelian. These are exactly the ambient hypotheses here. `def-sp-abelian` explicitly includes a zero object, finite biproducts and cokernels. Thus no existence claim about the finite sums or cokernel is taken merely from the module-object definition. The biproduct injection/projection identities and cokernel factorization condition are written inline as the meanings of those constructions, not new lemmas needing new nodes.

I tested the rank-zero cases before finalizing. With m=n=0 the cokernel is the zero module. With m=0, the zero map to R^n has cokernel R^n, so finite regular-module sums satisfy the predicate. With n=0 the cokernel is zero regardless of m. The identity of R has zero cokernel and causes no exclusion. In the ordinary example C=Ab, R=Z, the map multiplication by 2 gives Z/2, as the source intends. The zero ring object is allowed; its unital module objects are zero and the definition still works. No nonzero rank, injectivity of the presentation map, projectivity or uniqueness of rank has been added.

Against delivery-errors B through E: the item is self-contained and the categorical constructions are explicit; its source and blueprint ancestry are retained, with no fabricated Stacks tag; all searches are logged; no new nodes duplicate elementary facts or clauses of the item; the missing citation is repaired by reading and citing the exact existing abelianness statement; and the definition imposes the same hypotheses and predicate as the source. The category's finite biproducts and cokernels come from the named abelianness result, so no proof has been relocated into an unnamed or circular claim. The empty citations.json accurately reflects the absence of proof-step citations. I checked that all four statement dependencies exist and are unmerged and that none depends on this item. No imported `blueprint_*` or `import_flags` field has been changed.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against `def-sfb-finitely-presented-module.md` in the main-20261015 blueprint, hypothesis by hypothesis; the abelian monoidal setting, additive tensor, ring-object hypothesis, right-exactness, module-category cokernel presentation, and unrestricted natural ranks (including zero) agree.
- Proof steps: there are no proof steps because this node is a definition; consequently there are no step citations or elementary-step claims to validate.
- New nodes: there are no new nodes in this split; no B1–B7 form or duplicate-node review is applicable.
- Edge cases: checked ranks $(m,n)=(0,0),(0,n),(m,0)$, the identity and zero ring objects, and the ordinary case $(\mathcal C,R)=(\mathsf{Ab},\mathbf Z)$; the definition remains meaningful and agrees with the source in each case.
- Dependency statements: reread `def-sp-abelian`, `sk-def-sfb-ring-object`, `sk-def-sfb-module-objects`, and `lem-sfb-modobj-abelian`; each supplies exactly the ambient category, ring/module, regular-module, or abelianness fact used by the definition.
- Changes made in the second reading: none; the worker's repaired statement dependencies, explicit categorical universal properties, source metadata, and search log passed the audit and the delivery preflight.

## Second reading by Q67

- Item statement: reread `def-sfb-finitely-presented-module.md` in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/`; every hypothesis and clause agrees, including the abelian monoidal setting, additive and right-exact tensor, arbitrary natural ranks, and the module-category cokernel presentation.
- Proof steps: there are no proof steps for this definition; `proof` and `proof_deps` are empty, so no uncited argument or elementary-step claim is present.
- New nodes: none; therefore B1–B7, duplicate-node checks, and new-node search requirements are vacuous.
- Statement dependencies: reread `def-sp-abelian`, `sk-def-sfb-ring-object`, `sk-def-sfb-module-objects`, and `lem-sfb-modobj-abelian`; each statement supplies exactly the ambient category, ring/module objects, regular module, or abelianness used by the definition.
- Edge cases: checked ranks $(0,0)$, $(0,n)$, and $(m,0)$, the zero and identity ring objects, and $(\mathcal C,R)=(\mathsf{Ab},\mathbf Z)$; the predicate remains meaningful and unchanged.
- Delivery-errors B–E: the node is self-contained, has source and blueprint metadata, records actual searches, cites existing dependencies, and introduces no duplicate or hollow node.
- Changes in this second reading: appended this explicit audit section only; no node, statement, dependency, search record, or citation required repair.
