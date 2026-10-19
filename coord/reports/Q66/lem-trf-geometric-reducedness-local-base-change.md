# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-local-base-change.json`: statement retained verbatim; split into eight steps following Stacks 0384 and 035W. No Mathlib match for the whole assertion.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-finite-inseparable-test.json`: new statement-only node, status `unsplit`, the (1) iff (5) part of Stacks 030V. No Mathlib match.
- `citations.json`: literal statement quotations for all 23 step citations.
- `searches.jsonl`: ten actual search records from the prescribed search command, five for the item and five for the new test lemma, including a second semantic phrasing for each.

One new node, zero Mathlib leaves. No unit record is changed: the item is not the unit's key node.

## Attachments

None. I searched all `WeilConjectures/` by the item id and by geometric reducedness and read the relevant project extension files. The project has `AlgebraicGeometry.isReduced_baseChange` in `AlgebraicGeometry/Curve/RiemannRoch.lean:1584`, smooth and perfect-field geometric-reducedness results, and tensor reducedness over perfect fields in `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`. These neither state the equivalence for a single prime over an arbitrary field nor state the finite purely inseparable test. There is no exact project declaration to attach. Upstream master's unfinished declarations were not treated as proofs.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Audit findings and changes

The original item is correct and its statement is unchanged. The source is Varieties 0384 (`lemma-geometrically-reduced-upstairs`), expressed in local rings by 035W (`lemma-geometrically-reduced-at-point`). I read varieties.tex lines 354–391 and 491–522, and algebra.tex's 030V (`lemma-geometrically-reduced-finite-purely-inseparable-extension`), 0BRA (`lemma-p-ring-map`), and 033F (`lemma-descent-reduced`). The proof had been empty. I supplied the argument, all non-elementary citations, source places, proof origin, and blueprint provenance.

The existing `lem-weil-pbc-purely-inseparable-base-change-local-ring` and its residue helper require a Noetherian local algebra. Applying either would add an unavailable hypothesis. Instead step 2 applies the existing general power-generated spectrum theorem; locality is then a consequence of its homeomorphism. Likewise the nearby `lem-sc-etale-local-ring-stalk-faithfully-flat` assumes finite presentation and is not used. The flat-localization node actually used has a separate unrestricted first clause; its Noetherian conclusion is not invoked.

The inherited blueprint ancestry reaches `lem-trf-local-term-locality` through the geometric nodal-point branch. I read the current main-20261015 ancestor statement and proof and retained that ancestry. This item supplies the reducedness descent used by its immediate parent `lem-trf-geometric-field-stalk-descent` (the Curves 0C4D descent paragraph), rather than replacing the contracting-correspondence route of the unit. Whole-blueprint searches for geometric reducedness, purely inseparable extensions, reducedness and 030V found no exact blueprint duplicate of this item or of the new algebraic test.

## Not duplicates

- lem-trf-geometric-reducedness-finite-inseparable-test vs lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable: the existing node detects separability of a finite FIELD extension using a tensor with an algebraic closure. The new node tests reducedness of an ARBITRARY algebra under all field extensions using all finite purely inseparable extensions; it assumes no finite-dimensionality of that algebra and has no separability conclusion.
- lem-trf-geometric-reducedness-finite-inseparable-test vs lem-pc-inseparable-tensor-nilpotent: the existing node constructs a nonzero nilpotent from an inseparable element in a finite field extension. The new node is the general 030V equivalence for arbitrary commutative algebras, including the zero algebra. Neither existing statement implies it by specialization.

I searched the whole DAG by 030V and its label, and by geometric reducedness and finite purely inseparable extensions, before creating the node. The only existing source-tag matches are the two nodes just distinguished. Related geometric-regularity tests concern Noetherian regular rings, not reduced arbitrary algebras. The perfect-field reducedness results cannot handle the arbitrary ground field. The scalar-restriction and reduced-base-change nodes have different hypotheses and do not provide the finite-extension test. The new node is strictly an input to the descent proof: it says nothing about a prime of a scalar extension or the local rings compared by the item, so it does not restate either direction of the item.

## Review by Q66

I read the item against Varieties 0384 and 035W, including the absence of finite-type, Noetherian and closed-point assumptions. For X = Spec R the local rings are exactly A = R_p and B = (R tensor_k L)_q. Tag 035W identifies geometric reducedness at a point with the all-field-extension reducedness of that local ring, so both clauses in the item are precisely those of 0384. The prime q guarantees that the rings involved here are nonzero, but the test lemma independently allows the zero algebra. No statement dispute or target change is needed.

For step 1 I opened `lem-weil-pbc-localization-base-change` and `lem-weil-pbc-tensor-cancel-base-change`: the former states localization after arbitrary scalar extension, and the latter states exactly the cancellation isomorphism with its inverse. Apply them both for R to A and for S to B. The inclusion of denominators follows from contraction of q to p. Thus B tensor_L H is a further localization of A tensor_k H. The nilpotent-fraction argument is written explicitly, rather than citing a bare localization definition for reducedness preservation. H/L is also an extension of k, so condition (1) applies without another assumption.

For step 2 I opened the field-extension faithfully-flat statement and the universal-injectivity statement. They apply to arbitrary commutative algebras, so A to C is injective by taking the module A in the latter. I read the finite purely inseparable definition: in characteristic p each e has some p-power in k, and in characteristic zero E=k. The power-generated spectrum node actually states the homeomorphism when its kernel consists of nilpotents and the algebra generators have both the power and p-torsion conditions. Kernel zero, generators 1 tensor e, and p=0 in C verify these hypotheses explicitly. The final locality argument uses the specialization order of prime spectra: a homeomorphism preserves maximal prime ideals, and its only prime over the unique maximal ideal of A is the unique maximal ideal of C. It requires no finite-type or Noetherian claim. This uses the statement of the spectrum node, not a construction hidden in its proof.

For step 3 I opened `lem-weil-common-extension-fields`: it gives compatible embeddings of any TWO extensions, not just algebraic extensions. I checked the cancellation map so S tensor_L F is T as an S-algebra. The field-extension lemma gives faithful flatness and `lem-weil-pbc-faithfully-flat-surjective-spectrum` explicitly gives a prime Q contracting to the chosen q. Thus the common-extension point is constructed above the prescribed point, not just somewhere over p. These citations do not need a finiteness or smallness hypothesis.

For step 4 I checked localization-base-change again with S to B. Since Q contracts to q, every denominator used in B avoids Q. The further fraction localization is D and its reducedness follows from condition (2) applied to the actual extension F/L and the written nilpotent argument. No false assertion that an arbitrary quotient of a reduced ring is reduced is used.

For step 5 I checked the definition of prime localization (fractions, equality criterion, local maximal ideal) and localization-base-change. The inverse-image prime P contracts to p, and therefore extends to a prime of C contracting to m in A. Step 2 forces it to be C's maximal ideal. This is precisely why localization at P loses no elements of C: all newly inverted elements are already units. Both fraction maps and their composites are given, and they fix the structural maps to D. The comparison is an isomorphism of rings with the correct maps, not only an identification of underlying points.

For step 6 I opened `def-weil-pbc-faithfully-flat-ring-map`, `lem-weil-pbc-flat-local-ring-maps` and `lem-weil-pbc-flat-local-hom-faithfully-flat`. The definition includes that faithful flatness implies flatness; the localization node states flat local maps for ANY flat map and arbitrary primes, with Noetherianity only in a later optional clause. Here the map is the scalar extension F/E, and P is by construction the contracted prime. The last node assumes just two local rings and a flat local map, exactly what steps 2 and 5 have established. It therefore gives the faithful flatness needed in step 7.

For step 7 the universal-injectivity statement with N=C gives injection into C tensor_C D = D. Mapping a nilpotent and using injection is elementary and is written out. The source tag is 033F, checked in the tags mapping (I corrected an initial transcription 033E). For step 8 the new 030V node states exactly the finite test to arbitrary-field test, including the identity extension E=k and without a reducedness assumption on A. Thus it applies to the output of step 7 without additional input.

I checked the new statement against 030V (1) and (5), and read the source's proof: finite purely inseparable testing, finitely generated field reduction, a separating extension and preservation under separably generated extensions. Only the statement is delivered as a new node; this is non-elementary content that remains to be split later. Its notions are either explicitly defined (reducedness and the tensor multiplication) or cite the field-extension, finite-purely-inseparable and tensor definition nodes. The new lemma has neither proof steps nor hidden proof prose in its statement.

Small cases checked: R=0 has no q and makes the item vacuous; L=k gives the same local ring on both sides; R=k gives a field on both sides. In characteristic zero the identity extension in the new test says C is reduced, as required. For k=F_p(t) and C=k[u]/(u^p-t), the finite test fails for E=k(t^(1/p)), detecting the nonzero nilpotent u-t^(1/p); thus reducedness alone is not mistaken for geometric reducedness. The zero algebra satisfies both tests. Infinite polynomial algebras over k and their localizations are allowed: no step uses finite generation. If q lies on a nonclosed point, all contractions and localizations above still use that same prime; no maximality of p or q in R or S was assumed.

Mathlib searches used the required command, with results preserved verbatim in searches.jsonl and in node records. I read Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean, especially its explicit TODO comparing its algebraic-closure definition with all field extensions. The returned algebraic-extension instance, finite-subalgebra result, and formally-unramified reducedness theorem do not state the new test. I also read the project's similarly named extension file; its tensor-product theorems require a perfect ground field and give no attachment here. A second semantic phrasing for each node gave the same unsuitable family of results. No unavailable service was recorded as a negative search.

The general common-overfield theorem and the power-generated spectrum theorem are generic tools filed in other units. I declared their precise uses in split_report.tool_uses; they realize the 0384/035W proof's inputs and do not replace a step of the trace-formula unit. All other external theorem citations are Mathlib leaves. Every citation has its literal statement quoted in citations.json. The eight steps are all below 2000 characters, and none introduces a hidden unsupported comparison lemma. No elementary new node, same-clause helper, unsupported definition citation, cycle intentionally introduced, SGA reference, Lean edit, or compiler action is part of this delivery.

## Unfinished work

The single new 030V input remains `unsplit` as required for a one-level split. No part of this item's eight-step argument is left unfinished. The required remote dry run and push are the final validation and delivery operations.
