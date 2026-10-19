# Stage-1 report: sk-def-smooth

## Files written

- `dag/nodes/sec-smooth-base-change/sk-def-smooth.json`: definition and six proof steps for its factual assertions; split through existing nodes, with no exact whole-item Mathlib match.
- `dag/units/sk-def-smooth.json`: only the key unit's `realized` and `realized_by` fields are filled.
- `citations.json`: fourteen verbatim statement quotations, one for each node citation in the six steps.

There are 0 new nodes and 0 new Mathlib leaves. The imported item's `blueprint.is` remains `sk-def-smooth`, `from` remains null, and `same_as` is empty: related nodes cover individual notions and assertions, not the whole combined item.

## Attachments

`AlgebraicGeometry.Smooth` belongs to existing node `def-sbc-smooth-morphisms`. It is a Mathlib declaration and covers only the smoothness predicate, not this complete item. I searched the project declarations and blueprint tag in `WeilConjectures/`; there is no exact whole-item attachment. The project's `Scheme.IsTorsionSheafOfInvertibleOrder` and its colimit construction are relevant coefficient declarations, but do not attach the combined smoothness, arbitrary-base coefficient definition, affine-space assertion, example, and union assertion as a whole.

## WANTED:

None. The source passages used are present in the repository.

## Source error

STATEMENT-DISPUTED: the imported phrase "geometric fibres are smooth varieties" can impose a false finite-type or irreducibility requirement. For example, the morphism from the disjoint union of countably many copies of `Spec k` to `Spec k` is smooth: on each component it is the identity. Its geometric fibre is an infinite disjoint union of points, hence is not a variety of finite type. I replaced that phrase by the exact criterion already stated by `sbc-lem-smooth-criterion`: flatness, local finite presentation, and every scheme-theoretic residue-field fibre smooth over its residue field. This keeps the intended smoothness notion and does not add a finiteness hypothesis. The exact Stacks criterion is Tag 01V8, with the forward direction supplied by Tags 01VE, 01VF and 01VB.

The imported definition also contains mathematical assertions; leaving its proof empty would omit the filtered-union and comparison arguments. The all-positive-integer torsion union in `lemma-weil-pbc-torsion-filtered-union` does not itself establish the restricted union indexed by globally invertible integers. Those integers need not be cofinal among all positive integers. I therefore wrote the restricted argument in steps 3–5 instead of citing that lemma for a stronger conclusion. No new node restates a clause of the item.

## What I could not finish

Nothing remains in this stage-1 split. Proof formalization is outside the authorized stage. A second reader must review and deliver the accepted sandbox; I do not push it.

## Review by Q54

I read the current main-20261015 blueprint section for this item, its unit and chapter records, the relevant older blueprint child statements, and the statements of every cited DAG node. For the external mathematics I read `morphisms.tex` at the smooth-fibre criterion and its smoothness consequences (Tags 01V8, 01VB, 01VE and 01VF); `sites-modules.tex` at the abelian-sheaf limits and filtered-colimit lemma and the module forgetful functor lemmas (Tags 03CO, 03DA and 03DB); and `etale-cohomology.tex` at exactness of stalks and detection on stalks (Tags 03PT and 03PU) and the extension-by-zero stalk formula (Tag 03S5). There are no new nodes requiring additional source checks.

Step 1 takes the smoothness terminology from `def-sbc-smooth-morphisms` and the full equivalence from `sbc-lem-smooth-criterion`. I checked that the latter quantifies over arbitrary scheme morphisms and explicitly gives flatness, local finite presentation, and smooth residue-field fibres; it does not require a quasi-compact or finite-type morphism. The source error above is the correction made here.

Step 2 takes the full assertion, for every scheme and every nonnegative dimension, from `sbc-lem-affine-space-smooth`. Its conclusion is smoothness of relative dimension n. `def-sbc-smooth-morphisms` explicitly includes smoothness in that definition, which supplies exactly the implication used. The zero-dimensional case is included.

Step 3 takes the sectionwise kernel formula from `def-pur-abelian-sheaf-kernel`, preservation of kernels and existence of all small module-sheaf colimits from `lem-weil-pbc-module-sheaves-colimits-forgetful`, and the induced canonical map from `def-weil-pbc-category-colimit`. The small etale site meets the module lemma's sheafification hypothesis, and ordinary Lambda-module sheaves are the case of the constant ring sheaf. The indexing category is a set of positive integers, so it is small. I wrote the directedness and inclusion arguments explicitly: 1 is an index, products of indices remain globally invertible, and d dividing e gives F[d] contained in F[e]. These are elementary steps, not new nodes.

Step 4 uses the same module lemma for compatibility with abelian-sheaf colimits and `lem-weil-pbc-abelian-etale-sheaves-grothendieck` for exact filtered colimits. I checked the latter's statement actually asserts exactness for a small filtered diagram and preservation of the required objectwise monomorphism. The index constructed in step 3 satisfies those hypotheses. I corrected the step so monicity of each inclusion is attributed to its explicit inclusion construction in step 3, rather than to the module forgetful lemma. The identification of the constant-diagram colimit with F is proved explicitly using the common upper bounds, so this step does not assume a sectionwise description of arbitrary sheaf colimits.

Step 5 uses `prop-weil-pbc-geometric-stalks-exact` to identify kernel stalks and preserve the monomorphism, and `lemma-weil-pbc-geometric-stalk-conservative` to conclude that the underlying abelian-sheaf morphism is an isomorphism. Both statements are about the same small etale site and geometric stalks as the item. Allowed torsion gives an actual globally invertible index for each stalk element, so its lift lands in the diagram being used. The last Lambda-linearity argument upgrades the abelian inverse to a module-sheaf inverse and is written out. No unproved commutation of stalks with this colimit is needed.

Step 6 uses `lem-weil-pbc-constant-sheaf-geometric-stalk` with the abelian group Z/2, `lem-weil-pbc-extension-by-zero-stalks` with the open immersion D(2) into Spec Z, and `def-weil-affine-spectrum` for the global-section ring of Spec Z. I checked that the first lemma computes the constant-sheaf stalk, not just the constant presheaf, and that the second covers both the on-open and off-open cases. For a nonzero stalk one may choose the geometric generic point in D(2). On D(2), 2 is invertible; on the complement the stalk is zero and 1 suffices. The only positive global unit of Z is 1, which cannot kill a nonzero Z/2 element. Thus the example proves precisely the local-versus-global distinction claimed.

I checked the small cases: n=0; the zero sheaf; a base with no positive globally invertible integer except 1 (allowed torsion then forces every stalk, hence the sheaf, to vanish); and the empty base, whose zero global-section ring has 0=1 and where all positive integers satisfy the unit condition. The product-directedness argument and the proof remain valid in each case. No common annihilator, finite-generation hypothesis, or fixed torsion order is introduced.

For C1 and C4 of the delivery errors I matched each non-elementary inference with the statements above and copied their actual text into `citations.json`. I also checked B–E for self-contained statements, complete proofs, source places, coefficient categories, route declarations, blueprint metadata, and Mathlib search evidence. No node is elementary, duplicated, or a clause-restatement because none was created. The item records the searches actually run through `msearch.py`, including the invalid query and invalid directory attempt as such; later valid alternate queries supply the missing evidence. Search hits for the smooth predicate do not cover the complete item. The off-unit exactness and stalk facts are declared as generic tools in `split_report.tool_uses`.

## Second reading by Q54

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md`, the unit record, and the imported definition dependencies; the arbitrary-scheme hypotheses, coefficient categories, global-unit quantifier, all `n\in\mathbb N` cases, and restricted divisibility index are present. Verdict: pass after the recorded `STATEMENT-DISPUTED` correction of “smooth varieties” to the precise flat/locally-finite-presentation/smooth-fibre criterion.
- Step 1: checked against Stacks `morphisms.tex` Tags 01V8, 01VE, 01VF, 01VB and the statements of `def-sbc-smooth-morphisms` and `sbc-lem-smooth-criterion`; the criterion applies to arbitrary morphisms and supplies exactly the three clauses. Verdict: pass.
- Step 2: checked against the current blueprint affine-space paragraph and `sbc-lem-affine-space-smooth`; `def-sbc-smooth-morphisms` supplies the implication from relative-dimension smoothness, including `n=0`. Verdict: pass.
- Step 3: checked against `sites-modules.tex` Tags 03DA and 03DB and the exact statements of `def-pur-abelian-sheaf-kernel`, `lem-weil-pbc-module-sheaves-colimits-forgetful`, and `def-weil-pbc-category-colimit`; closure, divisibility inclusions, nonemptiness, product upper bounds, smallness, and the canonical cocone are all written out. Verdict: pass.
- Step 4: checked against `sites-modules.tex` Tag 03CO and the statements of `lem-weil-pbc-module-sheaves-colimits-forgetful` and `lem-weil-pbc-abelian-etale-sheaves-grothendieck`; the filtered-colimit monomorphism argument and the constant-diagram colimit identification are explicit. Verdict: pass.
- Step 5: checked against `etale-cohomology.tex` Tags 03PT and 03PU and the statements of `prop-weil-pbc-geometric-stalks-exact` and `lemma-weil-pbc-geometric-stalk-conservative`; stalk surjectivity, injectivity, and the final Lambda-linearity argument are supplied without assuming stalk-colimit commutation. Verdict: pass.
- Step 6: checked against `etale-cohomology.tex` Tag 03S5 and the statements of `lem-weil-pbc-constant-sheaf-geometric-stalk`, `lem-weil-pbc-extension-by-zero-stalks`, and `def-weil-affine-spectrum`; the on-open/off-open stalk cases and the fact that only 1 is a positive unit of `\mathbb Z` establish the comparison example. Verdict: pass.
- New nodes: none; consequently there are no new-node statements, searches, or Mathlib leaves to audit, and no duplicate or elementary child was introduced.

I repaired no mathematical step in this second reading. I verified that every citation quote is byte-for-byte the cited node statement, that `proof_deps` is the union of the six steps' `uses`, and that the item remains within the declared generic-tool route. I rechecked zero sheaf, zero-dimensional affine space, an empty scheme, a base whose only positive global unit is 1, and `S=\operatorname{Spec}\mathbb Z`; no edge case changes the conclusion. The source-error correction is retained and explicitly disclosed above; no other source or statement error was found.
