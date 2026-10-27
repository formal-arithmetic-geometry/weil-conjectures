# Q68: lem-sfb-stack-qcoh-abelian

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcoh-abelian.json`: existing statement, unchanged; four-step split following Stacks 06WV(2).
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-groupoid-abelian.json`: statement-only supporting theorem, unsplit; abelianity and underlying kernels/cokernels for quasi-coherent modules on a groupoid in algebraic spaces with flat source and target. Mathlib searches found ambient sheaf-module results, not this assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-preadditive-abelian-equivalence.json`: Mathlib leaf, `CategoryTheory.abelianOfEquivalence`, `Mathlib/CategoryTheory/Abelian/Transfer.lean:112` (complete declaration at lines 112–116). Includes its actual finite-products hypothesis.
- `citations.json`: one verbatim statement quotation for every citation in every item proof step.
- `searches.jsonl`: generated only by the required msearch command. The unsuccessful guessed names and ancillary finite-limit searches are retained. The JSON nodes record the relevant actual queries with their verdicts.

## Attachments

None. Searched the current project's `lean/WeilConjectures/` for the item's blueprint tag, algebraic-stack names, and groupoid abelianity, and read the relevant module category source. No project declaration states the item. General scheme-module abelianity is not this item. No Lean was written or compiled.

## WANTED

None. The needed Stacks TeX files and Mathlib declarations are available locally.

## Corrections and route

The imported statement is correct and was kept verbatim, including universes and the absence of Noetherian or finiteness hypotheses. Its proof was empty. The source expressly warns that inclusion into all big-fppf module sheaves is generally not exact; treating ambient kernels as quasi-coherent would therefore be an incorrect proof. The split uses the source's actual route through a smooth presentation, descent data, and flat groupoid abelianity.

Read the chapter record, the unit record and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. This auxiliary statement supports the existing adequate-algebra image-factorization branch below the alteration input, as the item's inherited `blueprint.from.place` records; it does not replace the unit's six-functor route. The supplied item's nearest blueprint ancestor is null according to `tools/blueprint_refs.py ancestor`; the new nodes retain that ancestry and extend its `via` chain. Searched the whole blueprint using `blueprint_refs.py search` for groupoids, quasi-coherent modules, flat groupoids, 06VZ, 06WV, 077S, preadditive categories, abelian equivalence and 03A3. No imported blueprint node states either new result. The existing live DAG already supplies the smooth-atlas module equivalence and its presentation geometry, so these were reused.

The transfer leaf is not an unproved geometric input: it is exactly Mathlib's categorical theorem. Its earlier semantic hit was read rather than accepting the search description, and its finite-products hypothesis is verified separately by the explicit Hom universal-property argument in step 3. No finiteness condition on the atlas or its relation space is introduced. No statement disputes or source errors were found.

## Unfinished work

Nothing is left unfinished in the item's one-level split. The flat algebraic-space groupoid lemma is deliberately statement-only, as required for a new non-Mathlib child. Its future split follows the kernels/cokernels argument in Stacks 06VZ: flat pullback gives the two induced isomorphisms, universal properties give descent and the two universal arrows, and the coimage-image comparison is an isomorphism on the underlying space. This future proof is not inserted into the child's statement or proof fields.

## Not duplicates

lem-sfb-flat-space-groupoid-abelian vs lem-sfb-groupoid-module-limits-colimits: the existing result assumes a groupoid in schemes; the new result permits algebraic spaces for both objects and arrows. A general algebraic-stack atlas has an algebraic-space relation, which need not be a scheme. Extending from schemes requires descent, not a one-line specialization.

lem-sfb-flat-space-groupoid-abelian vs lem-sfb-space-groupoid-module-descent: the existing result is the equivalence between stack modules and groupoid data with no flatness assumption; it does not assert abelianity or the construction of kernels in the datum category. The new result is the flatness-dependent algebraic-space groupoid theorem.

lem-sfb-flat-space-groupoid-abelian vs lem-sfb-smooth-atlas-module-descent: the existing result supplies an equivalence for a smooth atlas, with the displayed morphism and cocycle conventions. The new result supplies abelianity of the target datum category from flat projections; this is not a clause of that equivalence theorem.

lem-sfb-flat-space-groupoid-abelian vs lem-sfb-stack-qcoh-abelian: the item concerns modules on the big-fppf ringed site of an algebraic stack; the child concerns equivariant modules on small-etale algebraic-space sites. The equivalence connecting them is a separate substantive existing theorem, and the item's proof verifies the projection hypotheses and the datum convention before applying the child.

lem-sfb-preadditive-abelian-equivalence vs lem-sfb-abelian-sheaves-left-exact-reflector: both cite 03A3, but the existing result concerns sheaves valued in an abelian category and a left exact sheaf reflector; it does not state a transfer theorem for arbitrary equivalent categories. The new statement is the precise general Mathlib equivalence theorem, with preadditivity and finite products in the source.

## Review by Q68

I read the complete statement and proof of Stacks `stacks-sheaves.tex`, Tag 06WV, especially the proof of (2), and its preceding warning about nonexactness of the inclusion. I read Tag 06WT's statement and the descent construction in the live smooth-atlas-module-descent node, Stacks `algebraic.tex` Tag 04T5, and `spaces-morphisms.tex` Tag 04TA. For the new flat-groupoid node I read `spaces-groupoids.tex`, `definition-groupoid-module`, `lemma-isomorphism`, and the complete statement and proof of Tag 06VZ (`lemma-abelian`). Its source requires precisely flat source and target, not Noetherian or finite-type spaces. I read the existing algebraic-space groupoid definition, module-sheaf definition, quasi-coherence definition, tensor-pullback definition and flatness convention used in that node. For the new transfer leaf I read `homology.tex` Tag 03A3 (`lemma-adjoint-get-abelian`) and the exact Mathlib declaration at Transfer.lean lines 112–116, including its hypotheses. Mathlib's ambient `SheafOfModules.instAbelian` was also read: it concerns all module sheaves, which explains why the semantic hits do not finish the item or the flat-groupoid child.

In step 1, `def-sfb-algebraic-moduli-stack` actually supplies a smooth surjective scheme atlas. The statement of `lem-sfb-stack-chartwise-smooth-etale-calculus` makes it flat and locally finitely presented for representable maps. The statement of `lem-sfb-fppf-groupoid-stack-presentations`, clause (2), then supplies exactly the self-relation groupoid and the flat projections used next. I checked all these hypotheses against an arbitrary algebraic stack; no atlas quasi-compactness or scheme representability of the relation is used.

In step 2, the statement of `lem-sfb-smooth-atlas-module-descent` actually gives the equivalence on all module maps, the algebraic-space relation, and the displayed cocycle. The new flat-groupoid statement actually says its datum category is abelian. I checked that its direction of the comparison is the inverse of the atlas statement's direction: inverting delta changes delta_13 = delta_23 delta_12 to alpha_13 = alpha_12 alpha_23, and multiplying the morphism equation by the inverse data yields the child's commuting condition. Identity conditions agree. This removes a potential convention mismatch rather than silently identifying two differently defined categories.

Step 3 cites the actual preadditive definition for sectionwise Hom addition and the actual abelian definition for finite products in the target category. Its displayed natural Hom bijections prove the finite-product universal property after applying a quasi-inverse, including the empty product, without claiming an ambient-kernel closure theorem. This is a routine use of the definitions and the already obtained equivalence. Step 4 cites precisely the Mathlib leaf whose assumptions step 3 has established and concludes abelianity with the given additive structure.

I checked B–E of delivery-errors against these files. Both new statements introduce all their objects, cite their notions or define them inline, have single-escaped mathematical TeX after JSON decoding, and carry statement-only proof fields. Neither moves the whole item into a renaming: geometric descent remains an existing separate theorem, flatness is checked, the cocycle is compared, and the categorical transfer is a verified leaf. Every non-elementary item step has statement citations; every quote in citations.json is copied literally and locally checked as a substring. The union of the uses is the proof dependency list. Each step is shorter than 2000 characters.

I tested the geometric child on the unit groupoid of an arbitrary affine scheme, where it reduces to the usual module category, and on the empty groupoid, where it is the zero category. No Noetherian condition appears in either case. Tested the transfer leaf on the identity equivalence of a module category and on the zero category, including the empty finite product. As a check on the rejected ambient-kernel route, for X = Spec Z the kernel of multiplication by 2 on the structure sheaf of the big fppf site has zero restriction on X's small site but has nonzero value after the nonflat test Spec F_2; this cannot be the quasi-coherent kernel, which is zero. The presentation proof avoids that error throughout. All files written are in the assigned sandbox; the repository and launcher were read only.
