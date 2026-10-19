# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-exceptional-system-adjunction.json`: statement node; split into 16 proof steps; no Mathlib match.
- `citations.json`: a verbatim statement excerpt for every cited node in every step. When a step uses several clauses, its quote includes the full statement so the scope and hypotheses remain visible.
- `report.md`: this report.

## Attachments

None. Searched the read-only WeilConjectures source for the item tag and the exceptional/coefficient-system notions. `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek` and related finite functors in `WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean` cover finite preservation only. The normalized-system exceptional adjunction with its evaluation and triangle equations is not stated there. `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Adic.lean` contains sorry declarations for related tower realizations (lines 230, 274, 289, 337); none is an attachment.

## WANTED

None for this split.

## Audit of the imported node

The item is an extracted obligation, not an imported completed proof. Its statement and source explicitly separate the finite theorem (Bhatt–Scholze Lemma 6.7.18) from the coherent system strengthening. I retained that statement and its ancestry. The finite-field-only `lem-coef-finite-exceptional`, `lem-coef-finite-adjunction-diagram-realization` and `lem-pur-etale-coefficient-system-adjoint` cannot be applied to this arbitrary field. The general semilinear calculus expressly does not assert the required right adjoint on normalized systems. The proof now constructs a right adjoint on the entire derived strict-system category and identifies its evaluations with derived evaluation left extensions; restriction then supplies the item. No levelwise lifting or equality detection by evaluation is used.

## New nodes

None. All supporting statements already occur in the DAG. In particular the affine-space adjunction works over arbitrary Noetherian bases, and the closed Tor result accepts the open-image bounds and constructibility that the existing ordinary etale nodes provide. The elementary Kummer coefficient trace calculation remains a proof step, as required by the no-elementary-nodes rule.

## Not duplicates

No new-node pairs. Whole-DAG and blueprint searches included `exceptional adjunction`, `cartesian`, `quasi-excellent`, `finite Tor`, `affine-space projection`, `trace coefficient`, `affine-space trace`, `6.7.18`, and `normalized coefficient`. Existing general tools were reused. `blueprint_refs.py ancestor` returned `lem-per-artin-gabber-affine-curve`; the item already records the intermediate extracted nodes in `via`. No exact blueprint duplicate of the item was found.

## Mathlib searches

Read the inherited recorded searches, then ran the search command for the item with LeanFinder, Loogle, grep and LeanSearch. Also tried a second phrasing of the affine trace/coefficient question while deciding whether an auxiliary node was necessary. The actual logged query texts and results are preserved in `searches.jsonl` and appended to the item, without replacing the inherited records. Hits were ordinary sheaf/module adjunctions, algebraic etaleness and ring-theoretic traces; none states the exceptional normalized-system assertion. No service failure was represented as a negative match. There are no new nodes and no Mathlib leaves.

## Blueprint route and tool uses

This realizes the exceptional-adjunction ingredient of the historical Step 3 (Verdier duality) of `lem-per-artin-gabber-affine-curve`, through `lem-per-qbar-arbitrary-field-duality` and `lem-per-adic-exceptional-projection`. The current ancestor snapshot states the perverse claim without proof text; it does not contain the new system construction. This is recorded as an agent proof obligation, not attributed verbatim to the blueprint or to Bhatt–Scholze. Generic off-unit tools are declared individually in `split_report.tool_uses`. They construct the extracted finite exceptional ingredient and do not replace a step of the perverse/Fourier unit. No unit or chapter record was edited.

## Review by N8

I read Bhatt–Scholze, Lemmas 6.7.16–6.7.19, printed pp. 57–58. Lemma 6.7.18 has the finite restriction and extension squares; its proof uses a local closed/smooth factorization and the open-complement triangle. It does not assert an adjunction on the derived category of strict systems. I also read the current ancestor blueprint text and the affine-space adjunction/top-trace blueprint records. For the general categorical foundations I read Stacks Tag 0F5Y, `injectives-proposition-brown` (injectives.tex at line 2804), and Tag 0A8D, `derived-lemma-adjoint-is-exact` (derived.tex at line 2290). The finite smooth factor follows the existing projective-line/Kummer affine-space adjunction, with its explicitly normalized trace. No new source theorem or new node is introduced.

**Step 1.** Checked the valuation and finite-quotient conclusions against the DVR and finite-residue hypotheses. Positive valuation of ell gives an ell-power annihilator; it is invertible on k. The finite-type-over-Noetherian statement applies with Spec k and to the compactification. No hypothesis that k is finite, perfect or algebraically closed is introduced.

Cited statements read: `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients`, `lem-weil-l-adic-extension-absolute-value`, `lem-weil-pbc-finite-type-over-noetherian`.

**Step 2.** Checked that the semilinear statement supplies actual unbounded system functors, evaluations and open operations. The left-extension statement supplies Grothendieckness, evaluated coproducts and conservative evaluations. The proper-coproduct statement concerns ordinary etale finite rings on Noetherian schemes, exactly the case here. Thus Brown 0F5Y applies to the whole derived system category and supplies its actual triangle identities.

Cited statements read: `lem-coef-semilinear-derived-sections`, `lem-pur-system-level-left-extension`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-sf-exact-functor-derived-triangulated`, `lem-pc-right-derived-functor-triangulated`, `lem-amb-proper-coproducts`, `lem-grothendieck-derived-brown-right-adjoint`.

**Step 3.** Checked the ringed derived-composition statement with the two identity-topos coefficient morphisms. Proper projection is explicitly unbounded and includes the constant quotient module even though it is not flat. The open tensor theorem is also unbounded. Scalar restriction is exact and conservative because it leaves underlying complexes unchanged. The x tensor 1 computation fixes the comparison, its direction and its composition law.

Cited statements read: `lem-pur-derived-change-of-rings`, `lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-pc-pre-derived-adjoint-functors-general`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-amb-proper-coproducts-projection`, `lem-pur-etale-open-derived-tensor`.

**Step 4.** Checked the flat-model statement carefully: its constructible etale variant permits any Noetherian T with ell invertible, although its coefficient notation is introduced using a global datum. The separate residue Tor test applies to bounded constructible A_n-complexes. Finiteness is available over any field, for every finite commutative ring. Constructible kernels in the reduced bounded model use the constructible Serre statement. Quotient flatness is over the quotient ring; flatness of the quotient as an A_n-module is never claimed.

Cited statements read: `lem-fd-finite-ring-compact-support-finiteness`, `lem-sf-flat-model`, `lem-sf-reduction-flat-model`, `lem-exc-residue-tor-test`, `thm-constructible-serre`.

**Step 5.** Checked the ambient exceptional theorem has the supplied compactification and Noetherian hypotheses and is an ordinary etale assertion. The shift uniqueness statement supplies existence as well as uniqueness of the adjunction-compatible shifts; the right-adjoint exactness statement then applies. The mate definition gives precisely the item's displayed counit equation, with q inverse in the transpose.

Cited statements read: `thm-amb-etale-exceptional-adjoint`, `def-weil-pbc-adjunction-mate`, `lem-weil-pbc-adjunction-shift-compatibility-unique`, `lem-sf-triangulated-right-adjoint`.

**Step 6.** Opened the ordinary finite projective-line statement and the affine-space top-trace statement. The first explicitly defines h by scalar extension of a fixed Kummer class and trace by pr_2 b inverse; the second explicitly constructs the higher-dimensional adjunction by ordered affine-line composites. Reducing the two components of b and its inverse proves the trace equation in a few lines. This is an elementary step from these statements, not a new node for a clause of the item. It uses one common ell-power N, so nonflat quotient coefficients present no difficulty.

Cited statements read: `lem-asd-ordinary-finite-p1-adjunction`, `lem-amb-affine-space-top-trace`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-weil-pbc-mate-pasting`.

**Step 7.** Checked the affine-space adjunction is over arbitrary Noetherian S with invertible annihilator, on the whole ordinary etale categories. The Tate statement says the twists are locally free of rank one and defines them as mu_N tensor coefficients, sufficient for their coefficient comparison. Exact inverse image and flat pullback apply to the flat model; the constructible-stratum definition and constructible preimage statement justify the explicit finite-stratification argument. The preceding trace calculation identifies the isomorphism with the specified counit mate.

Cited statements read: `cor-amb-affine-space-adjunction`, `lem-sf-flat-model`, `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-ringed-topos-flat-module-pullback`, `lem-pur-scheme-constructible-preimage`, `def-weil-pbc-etale-constructible-sheaf`, `lem-asd-etale-finite-twist-pullback`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `def-weil-pbc-adjunction-mate`.

**Step 8.** Checked the two open-image statements give exactly what the closed Tor theorem assumes: a finite bound for every module sheaf, and constructibility of every higher image of a constructible sheaf. The complement of a closed immersion in the finite-type Noetherian ambient is quasi-compact. The closed theorem does not assume regularity or smoothness of the closed immersion.

Cited statements read: `det-geo-open-finiteness-ii-amplitude`, `cor-fin-deligne-open-finite-coefficients`, `prop-exc-closed-tor`.

**Step 9.** Checked coproduct preservation for the open direct image uses its finite cohomological dimension and qcqs, not just the definition of direct image. The constant-tensor lemma requires only countable coproducts and a finite constant module. The closed support triangle identifies its first arrow as the counit and its second as the unit. The rotated TR3 filler is identified with i_* b by the closed adjunction Hom bijection, which repairs a possible ambiguity in a triangle filler. Tensor exactness and the shift-compatible projection statement include the connecting map. Etale stalk statements justify the closed restriction retraction and conservativity; an initially considered pro-etale recollement citation was not retained.

Cited statements read: `lem-exc-direct-image-coproducts`, `lem-exc-constant-tensor`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-exc-closed-support-triangle`, `lem-amb-proper-coproducts-projection`, `lem-kun-derived-tensor-triangulated`, `lem-weil-pbc-ringed-projection-mate-exact`, `lem-sf-triangle-morphism-iso`, `lemma-weil-pbc-finite-stalk-formula`, `lemma-weil-pbc-geometric-stalk-conservative`, `prop-weil-pbc-geometric-stalks-exact`, `lem-weil-pbc-inverse-image-stalk-germ`, `prop-weil-pbc-inverse-image-modules-exact`, `def-weil-triangulated-category`.

**Step 10.** Checked the chart factorization includes finite covers of both the target and its inverse images, affine-space dimensions, and descent of finite cohomological and Tor intervals. Its finite-type and separated hypotheses hold. The unbounded compact-support composition/base-change statement and open adjunction give the left-functor identity Rf_! u_! = v_! Rh_!, whose right conjugate is the local exceptional identification. The empty-source clause is explicitly present in the chart lemma.

Cited statements read: `lem-sf-affine-chart-factorization-gluing`, `lem-amb-unbounded-compact-support-comparisons`, `lem-amb-etale-adjoint-locality`, `det-sp-unique-right-adjoint`, `lem-pur-site-restriction-module-adjunction-exact`.

**Step 11.** Checked mate pasting identifies actual comparison maps for the composite adjunction, rather than only objects. The composite counit calculation is given explicitly. The finite-cover chart clause and local vanishing of cohomology make the global comparison invertible. The finite-field-only exceptional comparison nodes were not used as general-field theorems.

Cited statements read: `lem-weil-pbc-mate-pasting`, `lem-sf-affine-chart-factorization-gluing`, `lem-amb-unbounded-compact-support-comparisons`, `def-weil-pbc-adjunction-mate`.

**Step 12.** Checked identity and composition clauses of the mate-pasting statement, and used both triangle identities in the unit calculation. The displayed unit equation is the correctly typed one with G_n(q) after b. The projection shift statement and uniqueness of the compatible right shift prove shift compatibility of the same maps.

Cited statements read: `lem-weil-pbc-mate-pasting`, `def-weil-pbc-adjunction-mate`, `lem-weil-pbc-adjunction-shift-compatibility-unique`, `lem-weil-pbc-ringed-projection-mate-exact`.

**Step 13.** Checked the derived evaluation left-extension statement supplies actual functors and adjunctions for nonflat ring maps and gives the sigma maps as natural transformations, not just component formulas. Theta is constructed by that adjunction, not chosen as a lift of its evaluations. Its evaluated coefficient map is the scalar-unit transpose of step 3. Equality of its compatibility words with sigma is proved by transposition.

Cited statements read: `lem-pur-system-level-left-extension`, `lem-pur-coefficient-evaluation-derived-left-adjoint`, `lem-coef-semilinear-derived-sections`.

**Step 14.** Checked every Hom in the displayed chain has the correct site and coefficient ring. Evaluation left adjunctions and the ambient finite adjunction give the claimed natural bijections. Inverse maps obtained from identities give the natural isomorphism. The sigma statement explicitly identifies precomposition with transition-adjoints; applying that identity to the Hom chain yields the displayed output transition. No faithfulness of evaluation on morphisms is assumed.

Cited statements read: `lem-pur-coefficient-evaluation-derived-left-adjoint`, `lem-coef-semilinear-derived-sections`, `thm-amb-etale-exceptional-adjoint`, `def-weil-pbc-adjunction-mate`.

**Step 15.** Checked both normalization arrows are isomorphisms and each output level is ctf before restricting the actual ambient adjunction. The constructible Serre theorem and exact tensor justify closure under triangles. Scalar linearity follows by the Hom bijection, and the cited shift/right-adjoint theorem proves exactness. All reasoning is levelwise in the bounds; none requires a bound independent of n or forms an integral inverse limit.

Cited statements read: `lem-coef-semilinear-derived-sections`, `lem-pur-system-level-left-extension`, `lem-kun-derived-tensor-triangulated`, `lem-weil-pbc-adjunction-shift-compatibility-unique`, `lem-sf-triangulated-right-adjoint`, `def-kun-tor-amplitude`, `def-weil-pbc-constructible-complexes`, `thm-constructible-serre`.

**Step 16.** Checked the unbounded compactification statement normalizes the comparison by the inverse proper open-restriction exchange. The semilinear statement constructs those same adjunction words on systems and says evaluation and pasting agree with the level words. Hence invertibility can be detected by evaluation while coherence is proved by mate-pasting identities before evaluation. Right-adjoint uniqueness identifies the resulting counit-preserving refinement isomorphisms and gives their cocycle.

Cited statements read: `lem-coef-semilinear-derived-sections`, `lem-amb-unbounded-compact-support-comparisons`, `lem-weil-pbc-mate-pasting`, `det-sp-unique-right-adjoint`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.

I checked B1–B10: no new unsplit nodes or restated clauses, no unintroduced new objects, preserved single TeX escaping and original item fields, no fabricated searches, and no possible full attachment. C1–C8 were checked by opening every cited statement and retaining only the ordinary-etale/general coefficient assertions that apply here; every proof use has a verbatim quotation in citations.json. D1–D5: the argument carries the system construction and the coefficient calculations, rather than moving an item clause to a child. E1–E7: every application uses finite rings, Noetherian finite-type schemes, quasi-compact open complements and the stated boundedness/constructibility conditions; the quotient maps are not assumed flat. No statement correction or disputed assertion was needed.

Small cases: empty X gives the zero source category and the zero exceptional functor; the chart descent statement covers it. The identity morphism gives identity compact support and its identity right adjoint. At n=1 the coefficient ring is the residue field; the Tor test and reduction argument still apply. At m=n, scalar units and their mates are identities. At affine dimension zero, the trace is the identity adjunction. Nonflat A_2 to A_1 is handled by derived tensor. Zero complexes and arbitrary shifts are included. A normalized input with bounds varying with n is admissible because Brown is first used on the unbounded system category and normalization is tested at each pair of levels.

Every proof step is shorter than 2000 characters. I inspected the Kummer trace step as well: it only reduces the two specified summands of the existing projective-line decomposition, then composes the existing coordinate adjunctions; it hides no new source lemma. The difficult derived-system comparison is written as the explicit theta construction, Hom chain, and sigma transition calculation.

## Unfinished work

No mathematical portion of this one-level split is left unrecorded. Existing cited nodes retain their own downstream stage-1 obligations; they were not edited.

## Validation

The first server check_dag run passed with no introduced finding. The required full delivery dry run and push results are recorded below after they exit.
