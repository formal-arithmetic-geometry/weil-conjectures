# Q58 stage-1 report: lem-trf-gauss-rational-function-stability

## Files written

All JSON files are under `dag/nodes/sec-trace-formula/` in this sandbox.

- `lem-trf-gauss-rational-function-stability.json`: item, statement retained, seven-step split.
- `lem-trf-gauss-spectral-coefficient-cartesian.json`: statement; no Mathlib match.
- `lem-trf-degree-filtration-rank-asymptotic.json`: statement; no Mathlib match.
- `lem-trf-spectral-reduction-dimension-criterion.json`: statement; no Mathlib match.
- `lem-trf-gauss-degree-filtration-reduction.json`: statement; no Mathlib match.
- `lem-trf-completed-algebraic-closure-cartesian.json`: statement; no Mathlib match.
- `lem-trf-cartesian-subspace-scalar-tower.json`: statement; no Mathlib match.
- `lem-trf-product-topology-spectral-uniqueness.json`: statement; no Mathlib match.

Seven new nodes, zero new Mathlib leaves. Each new node is statement-only, unsplit, with empty proof dependencies. `citations.json` records the exact statement quoted for every step/node pair. `searches.jsonl` is the search command's unmodified log; `search-results.txt` retains the outputs read, including second phrasings and targeted follow-ups. The query-plan files and write_split.py are sandbox working records, not delivery files.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item tag, Gauss/gauss, stable field, spectralNorm and spectralAlgNorm found no declaration proving the item. The existing Mathlib leaf `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed` is reused in Step 6; the search hit IsAlgClosed.lift did not become a duplicate node.

## Literature wanted

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Sections 5.3.3–5.3.4, printed pp.214–220, for lem-trf-gauss-rational-function-stability and its coefficient-cartesian, degree-growth and filtration-reduction inputs; Sections 2.4.1, 2.4.3, 2.5.1, 3.2.1, 3.4.1, 3.5.1 and 3.6.2 for the other four inputs. The archival PDF named in source.document is absent locally. I read the online primary scan at https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf rather than adding a document to the checkout. The assembly proof is marked agent-written, not an assertion that an archival document was present.

## Findings and changes

The imported item was unsplit, with no proof. Its statement agrees with the conclusion of BGR 5.3.4, not merely Proposition 5.3.3/3: the latter has a divisible-value-group assumption which the former removes. I retained the original statement, including arbitrary finite extensions and a possibly incomplete rational function field. There is no statement dispute or target alteration.

The proof first obtains equality of residue-algebra dimension and extension degree under divisibility. It then proves the constant-extension cartesianness by an explicit coefficient maximum calculation and descends through a finite compositum. The last step checks that the descended norm is the intrinsic spectral norm. An argument identifying these norms by complete-base uniqueness would be invalid over R; the product-topology uniqueness input has no completeness hypothesis.

The current latest blueprint uses contracting correspondences for local-term locality. This item is already an analytic support node in the historical normalization chain below that ancestor. The split preserves its chapter, unit and recorded ancestry and does not edit or substitute the latest unit proof. Whole-blueprint searches found no equivalent statement. No SGA source is used.

## What remains

No part of this stage-1 assembly is left unwritten. The seven statement-only inputs require subsequent stage-1 work; this delivery does not claim their proofs or any Lean implementation. Delivery validation is performed by the required remote dry run.

## Not duplicates

lem-trf-gauss-spectral-coefficient-cartesian vs lem-trf-gauss-rational-function-stability: the new lemma gives orthogonality only on finite k-subspaces, not an orthogonal R-basis; the dimension-growth argument remains necessary.

lem-trf-gauss-spectral-coefficient-cartesian vs lem-trf-tate-fraction-orthogonal-spectral-norm: polynomial rational functions with orthogonality over k differ from fraction fields of finite affinoid domains with orthogonality over the Tate fraction field; the latter is an ancestor depending on this route, not an input.

lem-trf-degree-filtration-rank-asymptotic vs lem-trf-gauss-rational-function-stability: the new lemma concerns total-degree growth of a normalization over an arbitrary coefficient field and a finite reduced algebra, with no Gauss valuation or stability conclusion.

lem-trf-spectral-reduction-dimension-criterion vs lem-trf-incomplete-spectral-algebra-norm: the existing leaf supplies the norm and its axioms, not the residue-dimension bound or orthonormal-basis equivalence.

lem-trf-spectral-reduction-dimension-criterion vs lem-trf-defectless-base-best-approximation: the existing best-approximation result assumes a complete base and a specified extension absolute value with ef equal to degree; the new result uses the spectral reduction algebra over an arbitrary possibly incomplete base and makes no best-approximation assertion.

lem-trf-gauss-degree-filtration-reduction vs lem-trf-degree-filtration-rank-asymptotic: the former compares Gauss reduction and a second, total-degree filtration; the latter computes growth without comparing two valuations.

lem-trf-completed-algebraic-closure-cartesian vs lem-trf-stable-field-completion: the existing result characterizes stability of a field by weak stability and its completion; it does not construct the completed algebraic closure or assert its cartesianness over k.

lem-trf-completed-algebraic-closure-cartesian vs lem-trf-dense-weak-stability-transfer: weak stability transferred along a dense inclusion is different from exact orthogonality of all finite k-subspaces of the completed algebraic closure.

lem-trf-cartesian-subspace-scalar-tower vs def-trf-stable-nonarchimedean-field: a definition of stability does not state subspace closure or transitivity of cartesian restriction of scalars.

lem-trf-product-topology-spectral-uniqueness vs lem-trf-incomplete-spectral-algebra-norm: constructing a spectral algebra norm does not identify another power-multiplicative product-topology norm with it.

lem-trf-product-topology-spectral-uniqueness vs lem-trf-weak-spectral-completion-product: the existing completion result compares spectral completions under weak stability; the new statement identifies a specified norm directly, under explicit two-sided coordinate bounds, without such an assumption.

## Review by Q58

I read the item and all seven new statements against the primary BGR scan. The item follows 5.3.3/3 and 5.3.4 together, printed pp.215–220. The coefficient-cartesian input is 5.3.3/2, pp.214–215: its scalar field is k, so it is genuinely weaker than stability over k(X). The growth formula is 5.3.3/4, pp.216–218; I retained the nonzero finite reduced algebra generality because the residue algebra need not be a field. The reduction comparison is the calculation following equation (4), pp.216–217, and has its own statement because it compares two independent spectral constructions and normalization rings. Its proof will need both integrality of minimal-polynomial coefficients and control of their degrees, not merely functoriality of reduction.

For the reduction criterion I read 3.2.1's power multiplicativity and 3.6.2/8, p.161, and its application in equations (2)–(3) of 5.3.3. The orthogonal-space part is the finite-dimensional reduction formula used there (2.5.1/6). The completed-closure input is exactly the combination of 3.4.1/3 and the cartesian completion criterion cited in 5.3.4, pp.218–219; I also read the completion/cartesian criterion in 2.4.3, p.102. The subspace and scalar-tower statements were checked in 2.4.1/5, p.96, and 2.4.3/4, p.100. Finally, I read 3.5.1/1, p.151, and its explicit application on p.220: the product topology, rather than completeness of the ground field, is the necessary hypothesis for spectral uniqueness here.

I reopened each cited DAG statement, including the existing algebraic-closure definition, embedding lemma, stable-field definition and incomplete spectral algebra norm leaf. In Step 1 no non-elementary assertion is hidden: reduction of normalized polynomials and the largest-monomial coefficient prove multiplicativity, and the quotient checks are written. In Step 2 the reduction criterion supplies precisely reducedness, finiteness and the dimension bound. The residual rational function field is identified by normalizing a denominator; this uses the Gauss coefficient formula, not a comparison of completions.

In Step 3 the growth lemma applies once to E and once to its nonzero reduced residue algebra D. The coefficient-cartesian lemma gives a basis of each finite k-space B(nu); it does not supply the desired R-basis. Divisibility is used exactly to make all its nonzero spectral values rescalable into the base value group, enabling the reduction-dimension equality. The filtration comparison supplies the injection, and the two asymptotic formulas turn it into the missing opposite inequality. Only the final clause of the reduction criterion supplies the R-basis. Thus none of these nodes restates the item, and the crucial dimension sandwich remains in the item's proof.

Step 4 uses the completed-closure statement with exactly the given complete, nontrivially valued stable k. Algebraic closedness supplies roots and excludes nontrivial finite algebraic extensions, so stability and value-group divisibility of k' follow directly. Step 5 spells out the common-denominator coefficient calculation; the subspace theorem is applied to the finite R-space W containing hU. It does not require R'/R finite. The subspace node states exactly this closure property.

In Step 6 the existing embedding lemma allows any algebraic E/R to embed into an algebraically closed extension of R. The finite R'-span is a subalgebra of a field, and injective multiplication on that finite space proves it is a field; no separate compositum lemma is needed. The tower node applies because Step 5 supplies cartesianness of R'/R and Step 4 supplies an orthogonal basis of E'/R'. Every finite R'-subspace of this finite orthogonal space has an orthogonal basis by clause (1) of that same cited node. This verifies the full hypothesis of clause (2).

Step 7 uses the existing spectral norm leaf for algebra-norm axioms and the reduction criterion for power multiplicativity. The displayed min/max bounds from the actual orthogonal basis verify the exact coordinate-topology hypothesis of the uniqueness statement. I do not assume that an arbitrary spectral norm restricts to the smaller field's spectral norm. That identification is the conclusion of the uniqueness node, after its hypotheses have been established.

For small cases I checked E=R, where the result and the dimension sandwich give rank one; F[X] itself, where dim B(nu)=binomial(nu+n,n) has leading term nu^n/n!; and products of two fields in the growth lemma, where both dimensions add. The residue algebra is deliberately allowed to be a product, rather than assumed a field. Zero vector subspaces use empty bases, whereas finite field extensions and the reduced algebra in the growth formula are nonzero. In characteristic p a purely inseparable extension generated by a p-th root still has the displayed spectral formula; none of the arguments asks for distinct roots or separability. The general descent is needed even for discretely valued k, whose value group is not divisible; no divisible-group assumption survives into the conclusion. For subspaces and tower restriction the weights need not lie in the base value group. The uniqueness statement does not assume normality and is applicable over the incomplete R.

I checked B–E of delivery-errors.md against these files: all notions are either defined inline or cite defining nodes, no new node contains a proof, no proof step exceeds 2000 characters, and every cited conclusion occurs verbatim in citations.json. Whole-DAG keyword/source searches, whole-blueprint searches and current project searches found no duplicate. Each new node has actual logged LeanFinder, Loogle, grep and LeanSearch queries, plus a second semantic phrasing. Hits for GramSchmidt concern inner products; PadicComplex concerns a particular base; IsIntegralClosure.rank is not the filtration limit; spectralNorm_unique assumes complete base. None states the new inputs under their hypotheses. The only exact generic embedding hit was already in the DAG and was reused. No independent worker was involved, as required by this direct-delivery brief.
