# Q68: lem-trf-valuation-rank-one-formal-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-rank-one-formal-comparison.json`: split into eleven steps. Original hypotheses and conclusions retained; appended inline explanations of height one, geometric reducedness, restricted series, topological presentation/generation, affinoid, boundedness and rank one. These clarify meanings without adding assumptions.
- `dag/nodes/sec-trace-formula/lem-trf-height-one-real-absolute-value.json`: statement-only, unsplit; no Mathlib match for deriving a real-valued absolute value from the ring-theoretic height-one assumption.
- `dag/nodes/sec-trace-formula/lem-trf-separable-monic-approximation.json`: statement-only, unsplit; no Mathlib match for separable monic density in arbitrary characteristic.
- `dag/nodes/sec-trace-formula/lem-trf-affinoid-polynomial-closed-point-comparison.json`: statement-only, unsplit; no Mathlib match for the Tate-algebra comparison with polynomial closed-point completions, including its analytic Noetherian/closed-ideal prerequisites.
- `citations.json`: one verbatim statement quotation per cited node per proof step.

There are three new nodes and zero new Mathlib leaves. No unit, chapter, live-project, launcher or Lean files were changed. The sandbox also holds the actual search log and a scratch script used to construct JSON.

## Attachments

None. Searched the exact blueprint tag and the valuation/completion, affinoid, Tate algebra and separable-approximation notions in `WeilConjectures/` in both named read-only checkouts. No declaration stating all of this item, or any new node, was found. The curve coheight-one DVR declaration is not this assertion. Upstream master is reference material, not evidence that its sorry declarations are proofs.

## Sources wanted

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Section 2.1 printed pp. 6–7 and Theorem 3.5.5 Step 3 printed pp. 22–23, for this item and all three new nodes. The primary PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online; the named local archival copy is absent. Nothing was downloaded or written into literature.

WANTED: Brian Conrad, *Completion of algebraic closure*, https://math.stanford.edu/~conrad/248APage/handouts/algclosurecomp.pdf, Theorem 1.1 and its coefficient/root-approximation proof, for background on the agent's completion argument. This online handout was read, but its theorem starts from an algebraically closed field. It is not cited as a theorem about completing a merely separably closed field.

## What needed expansion

The imported item had no proof. Temkin's Step 3 asserts the completed field, the flat topological model, reducedness via excellent algebraic local completions, scalar saturation, and the finite-module comparison. I expanded the completion and finite-presentation arguments rather than assuming completion exactness over a non-Noetherian valuation ring. I did not assume the original maps into completions were injective. The source's analytic identification of completed local rings remains a genuine separate lemma; moving reducedness or the entire formal-comparison clause into a new node would not be a split.

The scalar-saturation argument needs just a quotient modulo a power of pi contained in sV; it does not need a limiting equality to be lifted to an equality in E. The last clause needs finite presentation as an A-module, not just finiteness. Both hypotheses of the imported statement were retained.

Separably closed does not imply perfect or algebraically closed in positive characteristic. Mathlib's `IsAlgClosed.of_denseRange` has characteristic-zero and algebraically-closed-source hypotheses, so I did not use it. The new density node isolates the missing substantive approximation input and the item proves algebraic closure by a root-selection argument.

No statement dispute was found. No clause was dropped or weakened. The inline terminology added to the statement records the conventions used in the proof.

## Arguments for the new statement-only nodes

These arguments belong in this report, not in the unsplit nodes.

For the real-valued bridge, start from the ordered value group F*/V*. Prime ideals of a valuation ring correspond to convex subgroups, with the endpoints corresponding to the zero and maximal ideals (Temkin Section 2.1). Having no intermediate prime forces this nonzero ordered group to be archimedean: the elements bounded in absolute value by an integer multiple of any fixed positive element form a convex subgroup; if they were not the whole group they would give an intermediate one. The archimedean ordered-group embedding into the additive real numbers, followed by an exponential with reversed sign and value zero at zero, gives the required absolute value. This is a genuine order/valuation bridge, not a discreteness assertion. Mathlib's abstract rank-one equivalence assumes the archimedean-group hypothesis rather than proving it from the spectrum.

For separable-monic density, degree one is already separable. In degree greater than one, arbitrarily small distinct scalars exist by powers of an element of norm less than one. Perturb the linear coefficient by such a scalar, avoiding the at-most-one value making the derivative identically zero. The resulting nonzero derivative has finitely many roots in an algebraic closure. Now perturb the constant term, keeping it arbitrarily small and avoiding the finitely many values equal to minus the polynomial evaluated at one of these derivative roots. The perturbed polynomial has no common root with its derivative, hence is separable. Both perturbations preserve monicity and degree. This argument does not require a perfect or complete field. Temkin uses the completed ground field without spelling out this approximation; this node is expressly labelled an agent-supplied auxiliary statement, not falsely presented as a numbered theorem in that paper.

For the analytic comparison, the intended route is Tate-algebra Noetherianity and closed ideals, the affinoid closed-point theorem (finite residue extension), and the polynomial/restricted-series identification modulo successive powers of the closed-point ideal, followed by inverse limits and quotienting by J. These are real analytic algebra inputs, not properties of an arbitrary formal power-series ring. Temkin Step 3 explicitly uses this comparison for B=A tensor_V Khat and C=Ahat[1/pi]. Its new statement uses a complete nontrivially valued field and a polynomial ideal, and makes the closed-point rather than arbitrary-prime restriction explicit. No reducedness conclusion has been smuggled into it.

## Not duplicates

- `lem-trf-height-one-real-absolute-value` vs `lem-trf-valuation-rank-one-formal-comparison`: the new node only constructs a real absolute value from an arbitrary height-one valuation ring; it says nothing about completion, separable closedness, A or E. The item carries those arguments.
- `lem-trf-separable-monic-approximation` vs `lem-trf-separable-perturbation-factor-selection`: the existing node assumes a valuation on K(t) and a specified transcendental residue of f(t)/pi, and selects an irreducible separable factor preserving that residue. The new node gives coefficientwise approximation of every monic polynomial over an arbitrary nontrivially normed field; it has no residue-transcendence or irreducibility clause.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `lem-trf-valuation-grauert-remmert-powerbounded`: the latter is a finiteness theorem for power-bounded elements of a reduced affinoid algebra over an algebraically closed field. It neither supplies the polynomial local-completion comparison nor proves that a particular affinoid algebra is reduced.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `lem-trf-etale-completed-local-ring-iso`: the existing statement compares an etale morphism of finite-type schemes with equal residue fields. A Tate algebra is not a polynomial finite-type algebra, and the new comparison is analytic.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `lem-trf-isomorphism-completion-approximation`: the existing statement concerns approximating an already given local-completion isomorphism over a G-ring; it does not construct this analytic comparison.

Searched the entire DAG by statements as well as raw keywords/source names and searched the whole blueprint with `tools/blueprint_refs.py search` for affinoid, Tate algebra, valuation completion, real valuation, height-one, analytic completion, separable polynomial approximation, separable monic and completed local ring affinoid. There was no blueprint node stating any proposed new lemma. New blueprint ancestry is the item's existing ancestor `lem-trf-local-term-locality`, with the item prepended to the existing via chain. This is historical support for the imported normalization chain, not a replacement for the current contracting-correspondence route of unit sk-i-curve-zero.

## Mathlib searches

Every search in the node records was actually run through the required Q68 msearch command. `searches.jsonl` has 22 actual search calls. I read the hits and opened `Valuation/RankOne.lean`, `Valuation/Archimedean.lean`, `Analysis/Normed/Field/Dense.lean` and `Approximation.lean` for the plausible candidates. The records retain the exact query text, tool, source subdirectory, returned names/counts and log digest, with the substantive verdict. The item's inherited search history is retained.

Each new node has a plain-language LeanFinder search, a second plain-language phrasing, Loogle, a source grep and LeanSearch. The rank-one hits concern discrete valuations, a value group already assumed archimedean, or the reverse construction from a normed field. The polynomial approximation theorem preserves monicity and degree but not separability. `Dense.lean` expressly lists separable-monic density as missing. Formal-power-series Weierstrass results do not supply the Tate-algebra closed-point comparison. None is an exact match or a one-line specialization of a declaration found.

## Review by Q68

I read the primary Temkin PDF Section 2.1 and Theorem 3.5.5 Steps 0–5, especially Step 3, and the Conrad handout identified above. I checked the item's hypotheses against the source: nontrivial height one and a nonzero nonunit pi, flat finite-presentation models, geometrically reduced generic fibre, and a finite *finitely presented* intermediate A-module. The three auxiliary statements expose the valuation bridge, the arbitrary-characteristic approximation issue, and the exact analytic comparison used by the source. The density statement is an agent expansion, for which I supplied its argument above. The other two sources are described at their actual places, without invented Stacks tags for analytic theorems.

For step 1, the real-value node supplies precisely the absolute value and its unit ball. The completion definition supplies compatible residues; the conversion to Cauchy sequences, bounded-tail scaling and inverse formula are written out. Neither a uniformizer nor discrete values are used. Step 2 uses the new separable-density statement only over K, after finite coefficient approximation from Khat; the existing factorization node explicitly gives every linear factor over separably closed K. I checked the root bound and the product estimate choosing the next root, so the Cauchy selection is an actual induction with a base root.

For step 3, the flatness definition permits tensoring scalar injections, and the torsion-free-flat node applies to the valuation ring Vhat already constructed. The cancellation in each quotient is spelled out. For step 4, the existing inverse-limit node really has the short-exact-sequence conclusion when the *kernel* transitions are surjective; they are the residue maps of L, not an unspecified Mittag-Leffler assumption. The equality L intersect pi^n M=pi^n L proves all its levelwise hypotheses. This is a direct application plus a cancellation calculation, rather than a new completion-exactness black box.

For step 5, finite presentation supplies finitely many generators of I. Both needed quotients, A and I, are torsion-free over V; this is why step 4 applies twice. Coefficientwise inverse limits produce restricted series, not arbitrary power series. Step 6 applies the analytic node to precisely this quotient over the complete nontrivially normed Khat. Its statement supplies closedness, Noetherianity and a Banach quotient. The two unit-ball inclusions prove boundedness and the topology assertion; the pi-regularity from step 3 justifies localization injectivity.

For step 7, I opened every cited node statement. Fields-excellent and finite-type-localization-excellent yield excellence of B_p, the excellent-ring definition includes the G-ring property, and the G-ring definition explicitly makes the local-completion map regular. Localization-preserves-reduced applies because B is reduced by the geometric-reducedness hypothesis. Completion-Noetherian supplies the target Noetherian hypothesis of regular-map-reduced-target; both its source and target requirements are therefore met. The analytic comparison node gives the actual maximal-point completion isomorphism, not just an analogy of spectra. The Stacks places for these reused facts are 07QW (more-algebra-proposition-ubiquity-excellent), 07QU (more-algebra-lemma-finite-type-over-excellent), 07QK (more-algebra-lemma-reduced-goes-up) and 0316 (algebra-lemma-completion-Noetherian-Noetherian).

For step 8, localization-Noetherian applies to the Noetherian C from step 6, and Krull intersection 00IQ (algebra-lemma-intersection-powers-ideal-module) applies with R=M=C_m and I its maximal/Jacobson ideal. This proves the needed injection, rather than assuming it. The annihilator/maximal-ideal argument explains detection of a nonzero nilpotent explicitly. For step 9, completion-mod-power really supplies the coordinate projection to E/pi^N E for the finitely generated ideal (pi). Cofinality gives pi^N E contained in sE. Only this quotient equality is used; no original-ring injection is used.

For step 10, the finite-presentation definition really gives the displayed finite matrix. Its two quotient modules are torsion-free over V, so step 4 again applies. The common-cokernel argument proves the canonical tensor comparison without a Noetherian completion theorem. For step 11, the finite-generation statement supplies finitely many denominators, and K=V[1/pi] gives a common power of pi. The two actual maps i and j and their two compositions are stated; completing those identities and using pi-regularity proves both injection and localized isomorphism. It is not an unexplained 'clear denominators' step.

I checked the new nodes for B1–B9: self-contained statements, inline norm/Tate definitions, existing polynomial/separability/completion/localization definitions, empty proofs and proof dependencies, genuine searches and blueprint ancestry. For C1/C4 the cited statements were read, and `citations.json` quotes them verbatim; no cited proof is used as a substitute for its statement. The off-unit excellence, completion-Noetherian and tower-exactness results are explicitly declared generic tool uses in split_report, with their roles and the absence of a same-unit replacement. There is no citation of the parent normalization node, hence no introduced dependency cycle. For D1/D2 the item proves its actual clauses: none of the new nodes asserts a completion-field clause, reduced-model clause, scalar saturation, or finite-module comparison. No non-elementary step exceeds 2000 characters; I also checked the shorter steps for concealed comparisons. The only analytic comparison is isolated, while the presentation and residue calculations are written explicitly.

Small cases checked: a discrete valuation and a nondiscrete archimedean value group both satisfy the real-value bridge, but the trivial valuation is excluded; monic degree one needs no perturbation, and in characteristic p a polynomial T^p-a is made separable by a small nonzero linear term. For the analytic statement, n=0 gives a field or zero quotient; J=(T-a) with |a|>1 gives the zero Tate quotient and no maximal points, so no false faithful map B to C is asserted. For the item, A=V[T] gives the usual restricted algebra, A=0 gives zero completions, and A=V[1/pi]=V[T]/(pi T-1) is flat finitely presented but has zero completion. The latter case confirms why original completion maps must not be assumed injective. Scalar saturation still says sE=E there. Finite-intermediate-algebra denominators are a common pi-power only after taking the finite list of generators. No step requires V to be Noetherian or E to be adically separated.

This is direct delivery under the dispatcher brief, so this is my own signed review; no fictitious second worker or independent review is claimed. No prior returned-delivery points were supplied. The meaningful correction made while reviewing was to explain the terminology inline and to reject the tempting characteristic-zero Mathlib shortcut.

## Unfinished work

No stage-1 argument is left as an informal missing step. The three new nodes intentionally remain statement-only for later splitting. Their proofs are not claimed to exist in Lean, and no Lean or compiler was run. Maintainer independent review remains the delivery protocol's next review.

Additional duplicate-audit pairs required by the delivery tool (all share the historical source identifier 0707, but none states the proposed lemma):

- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `lem-trf-valuation-rank-one-formal-comparison`: the new node isolates the polynomial/Tate completed-local comparison over a complete valued field; the item also asserts valuation completion, flat models, reducedness, scalar saturation and finite-module comparison.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-birational-quasi-modification`: the definition concerns birational quasi-modifications of schemes, with no analytic algebra or completed local rings.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-centred-valuation`: the definition concerns a valuation centred on a scheme, with no Tate algebra or local-completion comparison.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-local-marking-length`: the definition concerns lengths of marked valuation data, with no polynomial/Tate algebra.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-modification`: the definition concerns scheme modifications, not analytic quotients or completed local rings.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-multipointed-curve-modification`: the definition concerns modifications of multipointed curves, not affinoid algebras.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-multipointed-curve`: the definition concerns multipointed curves, not Tate quotients or local completions.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-multipointed-eta-modification`: the definition concerns eta-modifications, not analytic closed points.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-nodal-dualizing-datum`: the definition concerns nodal dualizing data, not polynomial/Tate comparison.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-projective-line-tree`: the definition concerns projective-line trees, not affinoid local rings.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-rational-rank`: the definition concerns rational rank of a valuation, not Tate algebras or completions.
- `lem-trf-affinoid-polynomial-closed-point-comparison` vs `def-trf-schematically-dense-open`: the definition concerns schematically dense opens, not analytic local comparison.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-birational-quasi-modification`: the new lemma constructs a real absolute value from the two-prime spectrum of a valuation ring; the definition concerns birational scheme maps.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-centred-valuation`: the new lemma constructs the absolute value and unit ball; the definition only specifies a valuation centre on a scheme.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-local-marking-length`: the new lemma is a valuation-to-real bridge, while the definition concerns lengths of markings.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-modification`: the new lemma concerns a field valuation, while the definition concerns scheme modifications.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-multipointed-curve-modification`: the new lemma concerns the valuation spectrum, while the definition concerns curve modifications.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-multipointed-curve`: the new lemma constructs an absolute value, while the definition concerns a multipointed curve.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-multipointed-eta-modification`: the new lemma concerns ordered valuation groups, while the definition concerns eta-modifications.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-nodal-dualizing-datum`: the new lemma concerns valuations, while the definition concerns nodal dualizing data.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-projective-line-tree`: the new lemma concerns valuations, while the definition concerns a projective-line tree.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-rational-rank`: the new lemma is the real absolute-value construction under a height-one hypothesis; rational rank is only a valuation invariant and does not provide the construction.
- `lem-trf-separable-monic-approximation` vs `lem-trf-valuation-rank-one-formal-comparison`: the new node supplies only coefficientwise separable approximation; the item includes it as one ingredient of a much broader completion theorem.
- `lem-trf-separable-monic-approximation` vs `def-trf-birational-quasi-modification`: the new node concerns polynomial coefficients over a valued field; the definition concerns birational quasi-modifications.
- `lem-trf-separable-monic-approximation` vs `def-trf-centred-valuation`: the new node concerns separability and norm perturbations; the definition concerns a valuation centre.
- `lem-trf-separable-monic-approximation` vs `def-trf-local-marking-length`: the new node concerns polynomial approximation; the definition concerns marking lengths.
- `lem-trf-separable-monic-approximation` vs `def-trf-modification`: the new node concerns valued-field polynomials; the definition concerns scheme modifications.
- `lem-trf-separable-monic-approximation` vs `def-trf-multipointed-curve-modification`: the new node concerns separability, not modifications of multipointed curves.
- `lem-trf-separable-monic-approximation` vs `def-trf-multipointed-curve`: the new node concerns polynomials over a valued field, not curves.
- `lem-trf-separable-monic-approximation` vs `def-trf-multipointed-eta-modification`: the new node concerns polynomial coefficients, not eta-modifications.
- `lem-trf-separable-monic-approximation` vs `def-trf-nodal-dualizing-datum`: the new node concerns separable polynomials, not nodal dualizing data.
- `lem-trf-separable-monic-approximation` vs `def-trf-projective-line-tree`: the new node concerns polynomial perturbations, not projective-line trees.
- `lem-trf-separable-monic-approximation` vs `def-trf-rational-rank`: the new node concerns separability/density and does not define or compute rational rank.
- `lem-trf-separable-monic-approximation` vs `def-trf-schematically-dense-open`: the new node concerns valued polynomials, while the definition concerns dense opens of schemes.
- `lem-trf-height-one-real-absolute-value` vs `def-trf-schematically-dense-open`: the new lemma is a valuation-theoretic construction of a real absolute value and its unit ball; the definition concerns a schematically dense open subscheme and contains no valuation-group statement.
