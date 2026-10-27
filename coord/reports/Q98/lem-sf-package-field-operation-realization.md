# Q98 stage-1 delivery: lem-sf-package-field-operation-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-field-operation-realization.json`: existing statement node, now split in six steps; no whole-item Mathlib match.
- `citations.json`: 15 step/node entries with supporting verbatim statement excerpts.
- `report.md`: this report. `searches.jsonl` was written by the required search command; `write_split.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. The item's statement, source, chapter, unit, creation metadata and inherited Mathlib searches are preserved. No repository or launcher file was written, and no Lean or compiler tool was used.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, item id, rationalization, rational internal Hom/tensor and operation terminology. The exact tag has no hit. The rational-stage module `SixFunctors/Etale/Derived/RationalStage.lean` gives lattice/Hom/localization interfaces in its etale model, and contains a sorry for idempotent completeness; it does not state these five pro-etale operation comparisons together with common-stage evaluation compatibility. The ordinary upper-shriek rationalization is also only part of the item. Neither is an attachment for the whole statement.

## WANTED

None. This is an agent-written assembly of existing DAG statements and the supplied blueprint, not a claim that Stacks states this entire field-passage package.

## Findings and changes

The imported item had no proof. Its statement was not changed. Its preservation condition is used as a hypothesis throughout: the split does not prove integral preservation again. Fraction formulas are justified by the localization relation, not by assuming integral Hom modules are torsion-free. Common-stage operations are defined on the literal pair category of `def-weil-algebraically-closed-coefficients`; none of the proof identifies it silently with the separate PBC pair category. Object independence means canonical isomorphism, while independence of arrow representatives means equality in the displayed colimit. The report makes this distinction explicit without changing the mathematical statement.

Read `dag/chapters/sec-six-functors.json` and `dag/units/sk-thm-sf-package.json`. The current item is a descendant of `prop-functor-package` through `lem-sf-package-coefficient-domain-realization`, not the unit's key node, so no unit realization fields are edited. The unit record contains the older long package route; this item's exact route is the current ancestor's opening field-passage sentence, lines 7-8 of its main-20261015 proof. That sentence explicitly cites `lem-coef-rational-operations`. The proof follows its completed-integral, raw-rationalization, then common-finite-stage route.

The needed localization and operation-comparison tools already exist. No new lemma is necessary: separately linear extension of the two bifunctors and cancellation of common-stage comparison isomorphisms are written out as elementary steps instead of creating duplicates. The off-unit statements are declared in `split_report.tool_uses`, with their specific uses. No maintainer-owned `tool_uses` field is set.

## Searches

Read all hits of six new searches, logged by msearch under Q98: LeanFinder in two phrasings (localizing integral constructible functors and descending finite-field operations; rationalizing completed tensor/Hom while preserving evaluation), LeanSearch for derived complete constructible operations and common finite fields, Loogle for `CategoryTheory.Functor.IsTriangulated`, grep `rationaliz|Rationaliz|internalHom|InternalHom` in CategoryTheory, and whole-Mathlib grep `Rationalization|derivedComplete|constructible.*[Ii]nternal|[Ii]nternal.*constructible`. The signatures concern ordinary light condensed closed categories, ordinary sheaf/module scalar actions, module localization, generic monoidal closed categories and generic triangulated functors. They do not state the complete item or a one-line specialization. All services answered; the last grep had zero hits. Inherited searches are retained verbatim, with these actual searches appended.

Searched the whole DAG by item id, coefficient passage, rationalization, internal Hom/evaluation, scalar extension and common-stage terminology. Ran `tools/blueprint_refs.py ancestor` on the item and blueprint searches for `rational operations`, `rational`, `common-stage`, `field passage`, and `coefficient passage`. The ancestor is `prop-functor-package`. The rational-operations node covers an identification used here; it does not state all unary operations and common-stage formulas. The general coefficient-comparison node is cited as an existing stronger tool rather than recreated. No blueprint node states exactly the whole item, so its `same_as` is empty.

## Not duplicates

No new nodes were created. In particular the split reuses `lem-pur-semilinear-scalar-localization`, `lem-coef-rational-operations`, `lem-fix-operation-reduction`, and `lem-weil-scalar-extension-composition` instead of introducing localized-operation or common-stage-evaluation restatements. The ancestor and parent are not cited as proof dependencies, which avoids a cycle. A read-only dependency traversal found no path from these tool nodes back to this item.

## Review by Q98

I read the current main-20261015 `prop-functor-package.proof.md` opening sentence and `lem-coef-rational-operations.md` with its entire proof. The latter uses completed tensor, identifies localized internal Hom by the tensor-Hom adjunction, and explicitly preserves evaluation under finite scalar extension. I also read the current `lem-fix-operation-reduction.proof.md` from the six-functors-basics chapter and the current DAG statement and final scalar/localization proof steps of that node. They provide operation comparisons and their tensor/evaluation normalization; their finite-quotient perfectness qualification is not a hypothesis on the integral/rational Hom assertion. No SGA reference is used. There are no new-node sources to review.

For step 1 I checked the statements of `def-weil-rationalization-karoubi`, `lem-pur-semilinear-scalar-localization`, `def-fix-six-functor-datum`, and `def-weil-integral-rational-qbar-compact-support`. Raw rationalization has the same objects and localized morphisms; semilinear localization applies with identity coefficient homomorphism; compact support is expressly the integral value viewed in the rationalized category. Integral preservation is assumed by the item. These statements justify each of the three unary object comparisons and extension to fractions. The proof does not take a finite-quotient formula to be a theorem about arbitrary coefficient change.

For step 2 I read the full rational-level paragraph of `def-weil-derived-pullback-tensor-hom`: it states exactly the separately linear tensor and contravariant/covariant Hom formulas used here. I checked the balancing relation in the raw-localization definition. Applying separate linearity carries a killed-denominator difference to a killed-denominator difference; composition multiplies scalar factors. This argument remains valid for torsion Hom modules. Both output objects are integral constructible by the hypothesis, so no completion or preservation lemma is hidden in the elementary step.

For step 3 I reread the entire statement of `lem-coef-rational-operations`, not just its displayed duality specialization. Its opening asserts the general internal-Hom identification, and its final sentence explicitly preserves evaluations. This is exactly the required map c. The displayed evaluation equation has source QK tensor QH and target QL: t goes from that source to Q of the integral completed tensor, so the equation is correctly oriented. Multiplying the integral naturality equation by the denominator factors proves naturality for fractional arrows. No perfectness of K is assumed or needed.

For step 4 I checked `lem-fix-operation-reduction`'s bounded integral, rationalization and common-stage clauses, and its tensor-associator/evaluation compatibility. I read the complete statement of `lem-weil-scalar-extension-composition`, which supplies the actual transition associators. The semilinear-localization statement expressly preserves identity, composition, whiskering and associator equations. For R_E to R_F the uniformizer image is nonzero in the finite field extension, hence invertible after rationalization. Only the applicable integral/field clauses are used: neither finite-quotient site-perfect Hom nor conditional exceptional adjoints enter the proof.

For step 5 I checked the literal object and Hom-colimit definition in `def-weil-algebraically-closed-coefficients`, together with the complete algebraically closed paragraph of `def-weil-derived-pullback-tensor-hom`. These specify exactly the conjugated arrow formula, including the contravariance of Hom and the need to put both inputs over their compositum. The step uses the comparisons and equations established in step 4, then proves equality of representatives by going to a further common field. Composition follows by explicit cancellation, not by citing a result about a different category.

For step 6 I checked that the pair-category Hom set accepts the finite-stage evaluation as an actual arrow and that `lem-fix-operation-reduction` preserves evaluations together with tensor associators. Thus enlargement gives the same arrow class. Functorial transport of input isomorphisms and evaluation's naturality/dinaturality give the comparison for different object representatives. This is the standard defining evaluation identity, rather than an assertion that evaluation is covariantly natural in its first argument. Evaluation is not computed by an infinite extension of coefficients on the ambient sheaf category.

I checked small cases: identity morphisms and E=F give identity fraction/transition comparisons; two successive extensions use precisely the specified associator; a zero or uniformizer-torsion integral input becomes zero after rationalization without breaking the formula; zero maps remain zero; identity common-stage arrows cancel their two comparisons; isomorphic representatives give mutually inverse output maps. Empty schemes cause no denominator or stage exception. No statement dispute was found.

Against delivery-errors B-E: all citations were checked against their statement text and recorded verbatim; every non-elementary step cites existing statement nodes; elementary steps contain the actual short algebraic argument; no new self-containedness/tag/duplicate/Mathlib-leaf obligations arise; no source proof was silently used as a stronger statement; no extra geometric, perfectness, or torsion-freeness hypothesis was added. Every proof step is shorter than 2000 characters. No unit/chapter route was replaced, and no new nodes merely repackage clauses of the item.

## Unfinished work

None in the stage-1 split. Delivery awaits the required server preflight/dry run and push; their results will be recorded below.
