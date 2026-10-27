# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tate-gauss-fraction-stability.json`: item, statement unchanged, split into five proof steps. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-gauss-rational-function-stability.json`: new statement-only node, unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-tate-fraction-weak-stability.json`: new statement-only node, unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-dense-weak-stability-transfer.json`: new statement-only node, unsplit, no Mathlib match.
- `citations.json`: seven step/node entries, each quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch results; all recorded searches were run. Rendered BGR pages are reading aids confined to this sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag, TateAlgebra/tateAlgebra, Gauss fraction stability, spectralNorm, orthogonal basis and weak stability. The arithmetic normalized polynomial Gauss lemma is about a different norm and different fields. There is no project declaration stating this item. The inherited item has no attached Lean declaration.

## Wanted literature

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, archival copy at `literature/bosch-guentzer-remmert-nonarchimedean-analysis.pdf`, especially 3.5.2/1, 3.6.1/1, 3.6.2/3, 5.1.2/1, 5.3.1/1, 5.3.2/3 and 5.3.3–5.3.4, for the item and all three new nodes. The file is absent from the shared literature directory. I read the primary Arizona scan online, rendering pages only inside this sandbox. No PDF was installed into the repository. The item is honestly marked proof_origin.by = agent for the source-guided assembly and the explicit fraction/density calculations.

## Findings and changes

The item is mathematically correct, including e=0. Its source does not assert that the fraction field is complete, and I have not inferred completeness or a multiplicative extension spectral norm. Stability here is BGR's cartesian condition for the minimal-polynomial spectral norm, exactly the existing definition node, even when the base fraction field is incomplete. There is no statement correction or STATEMENT-DISPUTED.

The source's proof is not simply an application of its final Stability Theorem. On printed p.214 (PDF p.220), BGR reduces the Tate fraction field to the distinct rational function field by density, its independently proved weak stability, and the completion criterion. I retained this reduction instead of introducing a new node asserting the same conclusion as the item. The new rational-field node isolates Sections 5.3.3–5.3.4: Proposition 5.3.3/3 alone assumes a divisible value group, so the new node explicitly cites and uses the removal of that restriction at the end of 5.3.4 (printed p.220). The weak-stability node requires no stable ground field and asserts coordinate norm equivalence rather than existence of an exactly orthogonal basis. The dense-transfer node concerns arbitrary dense extensions of valued fields, not Tate algebras.

The local literature lacks BGR, but a primary scan was available. I inspected printed pp.151–159, 193, 212–215 and 218–220 relevant to the statements and reduction. The scan page offset changes: printed p.158 is PDF p.166, while printed p.214 is PDF p.220. Every source place records the appropriate offset. No SGA source is used.

The latest blueprint is `literature/blueprint/latest` -> `main-20261024`, commit ef6f9619fdbffa59e88528fb56483d76c70258c8. I read the current `lem-trf-local-term-locality` statement and proof and the item unit/chapter records. This analytic branch is inherited historical support beneath that node, not a replacement of the current contracting-correspondence argument. The item is not a unit key statement, so no unit realization file is changed.

## Searches and reuse

I searched the whole DAG by Gauss, cartesian normed spaces, stable nonarchimedean fields, weak stability, completion criteria and the BGR theorem numbers. Whole-blueprint searches using `tools/blueprint_refs.py search` covered Gauss, stable, weakly, rational function, spectral norm and nonarchimedean. No blueprint node states any of the three new lemmas. The ancestor command confirms `lem-trf-local-term-locality`; new from.via begins with this item and preserves all its inherited ancestors.

I reused `lem-trf-tate-gauss-multiplicative` and `lem-trf-restricted-series-gauss-completion` after opening their statements; the former already proves the multiplicativity required here, and the latter explicitly provides the elementary norm axioms and convergence of total-degree truncations. I did not create another Gauss-norm lemma or a separate elementary fraction/density node.

Each new node has leanfinder, leansearch, loogle and Mathlib grep queries in `searches.jsonl`, with two semantic phrasings. The transfer node has extra queries for its actual dense-inclusion form. All services answered; none is recorded unavailable. I read the returned hits. SpectralNorm.lean defines the spectral algebra norm but does not provide exact orthogonal bases; its completeSpace theorem requires the base complete, which is not the fraction field hypothesis here. FunctionField's infinite valuation is a degree valuation; LaurentSeries.RatFuncAdicCompl uses the X-adic valuation, not the Gauss norm. Inner-product Gram–Schmidt and arithmetic bases do not imply cartesian ultrametric field extensions. The completion instances preserve nonarchimedean topology, not stability. DenselyNormedField concerns norm values rather than density of one field inside another. Accordingly all three nodes remain unsplit, with no Mathlib match and no proof sketch hidden in their statements.

## Not duplicates

`lem-trf-gauss-rational-function-stability` vs `lem-trf-tate-gauss-fraction-stability`: the former concerns fractions of finite polynomials, a dense proper subfield of the analytic fraction field in general; passing to the latter additionally needs weak stability. It neither restates nor implies the item by a one-line specialization.

`lem-trf-tate-fraction-weak-stability` vs `lem-trf-tate-gauss-fraction-stability`: the former holds for every complete ground field, with no stability assumption, and asserts only equivalence to a coordinate norm on finite spectral extensions. It supplies no exact orthogonal basis and cannot give the item alone.

`lem-trf-dense-weak-stability-transfer` vs `lem-trf-tate-gauss-fraction-stability`: the former is a generic valued-field transfer statement with hypotheses of a stable dense subfield and weak stability. It contains no restricted-series or Gauss construction.

`lem-trf-gauss-rational-function-stability` vs `lem-trf-analytic-type23-stability`: the existing node assumes an algebraically closed base and complete one-dimensional analytic fields, and concludes a degree formula for extending valuations. The new node allows arbitrary complete stable bases and multiple variables and uses an incomplete rational field with the spectral norm.

`lem-trf-tate-fraction-weak-stability` vs `lem-trf-tate-gauss-multiplicative`: multiplicativity on the restricted-series ring says nothing about the topology on finite spectral extensions of its fraction field.

`lem-trf-dense-weak-stability-transfer` vs `lem-trf-incomplete-spectral-algebra-norm`: the existing Mathlib leaf defines the spectral norm and proves its norm axioms; it supplies no orthogonal bases and no dense-field stability transfer.

## What remains

The three new statement-only lemmas are intentionally not split at this one-level stage. No part of the item's assembly proof is left open. There are no proposed off-unit tool uses: all cited statements are in this item's unit, and the generic spectral norm is an existing Mathlib leaf. No Lean was written and no compiler, Lake or build command was run.

## Review by Q29

I checked this split myself against delivery-errors B–E with the source and cited statements open. This is the author's review under the direct-delivery brief; independent review belongs to the maintainer.

For the item, BGR 5.1.2/1 (printed p.193) gives Gauss multiplicativity, and 5.3.2/1 (printed p.213) states the stability assertion. Its proof reduction at 5.3.2/3 (printed p.214) uses precisely rational-field stability, common completion and weak stability. The definition at 3.6.1/1 (printed p.156) agrees with `def-trf-stable-nonarchimedean-field`: a finite extension carries its spectral norm and must admit an orthogonal basis. This is not an assertion of a unique multiplicative valuation on finite extensions of the incomplete field.

Step 1 uses the stability definition only for the zero-variable identity case. I opened `lem-trf-restricted-series-gauss-completion`: its statement explicitly includes finite-valuedness, definiteness, normalization, negation and the strong triangle inequality, exactly the properties invoked. I opened `lem-trf-tate-gauss-multiplicative`: it says G(fg)=G(f)G(g) for restricted families, including e=0, so positivity of both factors proves the domain assertion. The domain deduction is written out and does not import a separate integral-domain theorem.

Step 2 cites no node because it is a direct calculation from step 1 and the field-of-fractions equivalence relation. I checked cross multiplication, positivity of the denominators, the product formula and the common-denominator estimate for sums. Definite zero and extension along the constant embedding are explicit, so no valued-field axiom is suppressed. This step is elementary, not a new node that repeats one of the item's clauses.

Step 3 uses only the statement of the new rational-field node. Its hypotheses match k's completeness, nontrivial norm and stability; the e=0 case has already been discharged. I checked its source: the divisible-group Proposition 5.3.3/3 at printed p.215 is insufficient alone, but Section 5.3.4 at printed pp.218–220 concludes the general rational-field stability after adjoining the completed algebraic closure and descending the spectral norm. The new node cites both. The injection of finite-support families identifies polynomial coefficients literally, so the norm restricted from F is exactly the new node's Gauss norm. There is no identification of all restricted series with polynomials.

Step 4 uses the truncation-convergence clause of `lem-trf-restricted-series-gauss-completion`, which I read verbatim. All remaining estimates follow from already established ultrametricity and multiplicativity: the error smaller than G(b) forces G(q_N)=G(b); truncation cannot increase G(p_N); the displayed difference identity gives two terms tending to zero over fixed positive denominators. Thus the step proves density for fractions themselves, not only for the Tate ring. It is marked elementary with its cited convergence input; no hidden completion isomorphism is used here.

Step 5 uses the whole statement of `lem-trf-tate-fraction-weak-stability`. BGR 5.3.1/1, printed pp.212–213, requires arbitrary complete k, not stable k, and its weak-cartesian meaning is the product topology from 3.5.2/1 and 3.5.1 (printed pp.151–153). The two-sided constants in the node spell out that topology for any finite basis; I checked they do not claim equality with a maximum. The norm is the minimal-polynomial spectral norm already supplied by the existing leaf. The generic transfer node assumes this very same pair of coordinate inequalities, together with density and stability of R, all already established. Its source 3.6.2/3, printed p.158, states stable iff weakly stable with stable completion. Density identifies the completions isometrically, so stable R gives the common stable completion and weakly stable F gives stable F. This is the generic argument used by BGR 5.3.2/3, not an uncited consequence of a definition. No completeness of F is inferred.

For all three new nodes I checked self-contained objects, exact norm choices, finite-extension quantifiers, no separability restriction, empty proof/proof_deps and source place. They are neither elementary calculations nor duplicate final clauses. There are no Stacks tags to match: these are BGR analytic results, and inventing a Stacks source would be false attribution. Their blueprint provenance follows the ancestor command and whole-blueprint search, with same_as=[] after those searches.

Small cases checked: e=0 reduces to the given k; the fraction formula at a=0 and denominator 1; replacing a/b by ac/bc for c nonzero; cancellations in sums use only the ultrametric inequality; for a polynomial denominator, truncations eventually equal b; for a general denominator, equality of norms requires strict error <G(b), which is explicitly imposed. A finite extension of degree one satisfies the weak bounds with c=C=|w_1|. The transfer lemma with R=F reduces to the already assumed stability; its hypotheses do not assert that weak stability alone suffices. Nondivisible value groups are covered by 5.3.4, and purely inseparable finite extensions remain quantified in both stability and weak stability. I corrected the initial temptation to quote only the divisible-value-group proposition and to infer stability from the stable common completion without the independent weak-stability input. Every step is below 2000 characters, and every citation has its unmodified statement in citations.json.
