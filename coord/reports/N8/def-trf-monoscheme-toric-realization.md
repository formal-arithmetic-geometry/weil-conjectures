# Stage-1 report: def-trf-monoscheme-toric-realization

## Files written

- `dag/nodes/sec-trace-formula/def-trf-monoscheme-toric-realization.json`: definition, split; repaired torus and normalized-tower contraction clauses; no new child nodes and no Mathlib leaf.
- `citations.json`: empty, because the item is a definition and has no proof steps.
- `searches.jsonl`: changed-question Mathlib searches rerun with `msearch.py`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and for monoscheme, monoidal-space, Kato-fan, toric-realization, and monoid-spectrum terminology; no sorry-free project declaration states this definition. The imported definition remains a DAG definition rather than an attachment.

## WANTED

None. The cited source is present at `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs. I searched the whole DAG and blueprint for monoscheme, monoidal space, Kato fan, monoid spectrum, normalized blowup, and toric tower. The existing `def-trf-fine-fan-blowup` is the stated prerequisite and is cited rather than duplicated.

## Statement corrected

The returned review identified two source-faithfulness errors. First, ILO VIII §3.2.4 defines a toric scheme from a torsion-free connected monoscheme. The former sentence said that every connected component's generic group defines a torus, which is false for a torsion group: for the fine monoid with group completion \(P=\mathbf Z/2\mathbf Z\) over \(\mathbf Q\), the generic group algebra gives \(\mu_2\), not a split torus. I changed the sentence to “On each torsion-free connected component, the generic group … defines the split torus …”.

Second, the former phrase “contracts stages with unit ideal” would delete a nontrivial normalized stage. For \(A=\mathbf Q[t^2,t^3]\), the unit-ideal ordinary blowup is the identity but its normalization is \(\operatorname{Spec}\mathbf Q[t]\to\operatorname{Spec}A\), which is not an isomorphism. I changed the clause to omit a unit-ideal stage only when its normalized blowup morphism is an isomorphism, retaining this nontrivial normalization. This follows the contraction convention in ILO VIII §2.3.4 and the normalized-blowup definition in §§2.2.3–2.2.8.

The corrected statement is otherwise unchanged. Existing citers are `lem-trf-functorial-fan-desingularization`, `lem-trf-sharpening-fan-bijection`, `lem-trf-toric-monoid-comparison`, `lem-trf-toric-normalized-desingularization`, and `lem-trf-toric-realization-finite-type`; the correction only narrows the definition to the source's torsion-free toric setting and fixes the contraction convention they invoke.

## Review by N8

I read the corrected item, `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the blueprint ancestor `lem-trf-local-term-locality` in `literature/blueprint/main-20261015/`. I read Illusie–Laszlo–Orgogozo, Exposé VIII §§2.1.1–2.2.8, §2.3.4, §§3.1.3–3.1.22, §3.2.1–3.2.4 and §§3.2.14–3.2.15 (printed pp. 86–93 and 98–105). Those passages supply the monoidal-space charts, sharpening, smoothness, toric realization, torus condition, ideals, blowups, normalized blowups, pullbacks, and contraction behavior. No new node was created, so there are no new-node statements or proof steps to cite; the five existing statement dependencies were opened and each supplies exactly the definition clause named in the item.

I checked the hypotheses clause by clause. The torus paragraph now has both connectedness and torsion freeness, matching §3.2.4; the P=\(\mathbf Z/2\mathbf Z\) example tests the rejected unrestricted version. The normalized blowup paragraph explicitly distinguishes ordinary blowup from normalization and requires an isomorphism before contraction; the cusp ring \(\mathbf Q[t^2,t^3]\) tests that a unit ideal can still yield a non-isomorphic normalization. The fine-fan dependency's current contraction rule was reread and agrees with this qualification. The finite-affine-cover, field, reduced-toric-scheme, smooth-pullback, and regular-terminal-scheme hypotheses remain present. The changed Mathlib searches (LeanFinder, LeanSearch, Loogle, and Mathlib grep) returned only ordinary scheme normalization, integrality, or torsion-free algebra declarations, so this monoidal-geometric definition is not a Mathlib leaf.

## What was wrong or incomplete

The returned delivery correctly found E1/E2 and E2/E4 defects in the imported statement. I repaired both in the node and recorded the counterexamples above. The earlier report incorrectly said the statement was unchanged; this report replaces that claim and records the exact corrections. No Lean source declaration, Mathlib declaration, duplicate node, or missing citation was found.

## What remains

Nothing remains for this definition at stage 1 after the required dry run and delivery.
