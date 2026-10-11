# Stage 1 report

1. Files written: item `lem-sc-local-dvr-base-change` (statement, split); `lem-sc-rational-point-base-change-unique` (statement-only, Mathlib no match); `lem-sc-dvr-field-extension-order` (statement-only, Mathlib no match).
2. Attachments: none.
3. WANTED: none.
4. No existing declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carries the blueprint tag or the exact item. The existing `lem-sc-smooth-connected-curve-local-rings` node supplies the DVR and fraction-field facts for the original curve. The affine fibre calculation and the DVR scalar-extension calculation are separate smaller statements; neither was found elsewhere in the DAG or blueprint.
5. Nothing remains unfinished.

## Review by C1

I read the item source in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-ext-invariance/thm-sc-constant-invariance.md`, specifically the affine-case unit quotient paragraph. I also read `lem-sc-smooth-connected-curve-local-rings.json`, whose statement explicitly supplies that every closed-point local ring is a DVR with fraction field `k(C)` and normalized valuation. Step 1 uses the first new node exactly for the affine fibre calculation: because the residue field at a rational point is `k`, the tensor residue algebra is `k'`, hence the fibre has one point. Step 2 uses the existing curve node for the original DVR and the second new node for the localized tensor DVR, its surviving uniformizer, and equality of normalized exponents. Step 3 uses the existing fraction-field clause and the second node's exponent equality to identify the scalar-extension element with the pullback `f'` and obtain the displayed valuation equality. I checked the hypotheses in the affine chart (`A/𝔪 = k`), and tested the algebraic claims on `A = k[t]_(t)` (where the base change is `k'[t]_(t)` and `v(t^n u)=n`) and on `X = ℙ¹_k` at `0`. The required Lean searches were run for the item and both new nodes; LeanSearch was unavailable, and the recorded verdicts preserve that service failure rather than treating it as a negative result.

## Not duplicates

lem-sc-dvr-field-extension-order vs lem-sc-dvr-saturation-line-smith-normal-form: the existing node concerns Smith normal form saturation, while this node concerns scalar extension of a DVR along its residue-field extension and preservation of normalized exponents.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-z-localizations-dvr: the existing node constructs DVR localizations at primes in a localization argument; this node compares a DVR with its residue-field scalar extension.
lem-sc-dvr-field-extension-order vs def-weil-pbc-cohen-ring: the existing node defines Cohen rings; this node is a valuation-preservation statement for a tensor/localization.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-completion-of-dvr-is-dvr: the existing node concerns completions; this node concerns field-extension base change.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-serre-criterion-normal: the existing node is Serre's normality criterion; this node is a scalar-extension DVR computation.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-dvr-unit-times-uniformizer-power: the existing node factors elements in one DVR; this node compares the factor exponent before and after scalar extension.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-pid-noetherian-normal: the existing node characterizes PID normality; this node establishes a new DVR after residue-field extension.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-regular-local-dim-one-iff-normal: the existing node relates regularity and normality; this node is a base-change order comparison.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-principal-maximal-dim-one-regular: the existing node proves a regularity criterion; this node transports a uniformizer across scalar extension.
lem-sc-dvr-field-extension-order vs lem-weil-pbc-dvr-completion-regular: the existing node treats completion regularity; this node treats residue-field extension.
lem-sc-dvr-field-extension-order vs lem-exc-punctured-curve-branches: the existing node studies branches of punctured curves; this node compares DVR orders at one rational point.
lem-sc-dvr-field-extension-order vs def-sc-discrete-valuation-ring: the existing node is only the definition of a DVR; this node proves preservation under a specified tensor/localization.
lem-sc-rational-point-base-change-unique vs lem-sc-curve-base-change-relative-dimension-one: the existing node proves smoothness and fibre dimension after arbitrary scheme base change; this node proves uniqueness of the fibre point over a rational point by the residue-field tensor calculation.
lem-sc-rational-point-base-change-unique vs lem-sc-fibre-dimension-after-base-change: the existing node compares dimensions of fibres; this node identifies the underlying fibre as Spec of the extended residue field and hence a singleton.

## Second reading by C1

- Item statement: checked against the affine-case unit quotient paragraph of the blueprint; the rational-point, local-DVR, and normalized-order clauses match the hypotheses and conclusion used there.
- Step 1: checked the tensor calculation $(A/\\mathfrak m)\\otimes_k k'\\cong k'$; the cited uniqueness node states exactly the singleton fibre conclusion. The worker's Stacks 02FY citation was removed because 02FY is a fibre-dimension lemma, not this affine calculation.
- Step 2: checked the local-ring localization and residue-field hypothesis against the smooth-connected-curve local-rings node and the scalar-extension node; the latter is now stated in the constant-field setting actually used by the item.
- Step 3: checked the fraction-field identification and pullback of $f$ against the existing local-rings node and the exponent clause of the scalar-extension node; the elementary identification is stated explicitly.
- New node `lem-sc-rational-point-base-change-unique`: statement-only form, self-contained definitions cited, and edge cases $X=\\operatorname{Spec}k$ and the empty scheme checked. No Mathlib declaration gives the tensor-fibre uniqueness.
- New node `lem-sc-dvr-field-extension-order`: statement-only form, self-contained DVR and field-extension dependencies, and tests on $R=k[t]_{(t)}$, $k'=k$, and $f=t^n u$. No Mathlib declaration gives the scalar-extension order theorem.

Changes: corrected the item node's `created.item` to the delivered item; removed the incorrect 02FY source attribution; added the actual blueprint source for the elementary affine calculation; restricted the auxiliary DVR statement to a residue field equal to the constant algebraically closed field and recorded `def-pc-field-extension` as a dependency; clarified the fraction-field step. The source text of Stacks 00PD was read and confirms only the DVR characterization and unit-times-uniformizer factorization, so the tensor calculation remains an explicit elementary argument rather than a claim that 00PD states it.
