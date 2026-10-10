Files written:

- `lem-sc-pseudo-coherent-support-annihilation.json` (item, split)
- `lem-sc-rhom-supported-qcoherent.json` (statement, Mathlib no match)
- `lem-sc-supported-factor-through-thick.json` (statement, Mathlib no match)

Attachments: none.

WANTED: none.

What was wrong in the returned split: `lem-sc-supported-hocolim-compact-factor` falsely asserted that the stages were built by finite sums, shifts, and cones; Tag 09SN permits arbitrary coproducts. `lem-sc-supported-perfect-generator` and that hocolim node duplicated existing `lem-sc-supported-derived-generated-perfect` and `lem-pc-compact-hom-hocolim`. The old thick-factor node was not self-contained and used the wrong object. I deleted both duplicate nodes, corrected the internal-Hom source from Tag 0A9B to Tag 0A6H (with the support observation in Tag 0A9C), and replaced the old child with the generic Tag 09SP statement for a compact object mapping to a 09SN stage.

## Not duplicates

`lem-sc-rhom-supported-qcoherent` vs existing internal-Hom nodes: this statement combines the pseudo-coherent/perfect quasi-coherence alternatives with support on T; existing nodes only state stalk localization or affine comparisons.
`lem-sc-rhom-supported-qcoherent` vs `lem-sc-pseudo-coherent-rhom-qcoherent`: the existing node assumes a Noetherian scheme and a pseudo-coherent quasi-coherent algebra in the first argument, while this node works for any scheme, includes the perfect first-argument case, and adds support on a closed subset.
`lem-sc-rhom-supported-qcoherent` vs `lem-sc-affine-pseudo-coherent-rhom-qcoherent`: the existing node is an affine RHom comparison for bounded-above finite-projective complexes, while this node is the global scheme statement with both pseudo-coherent and perfect cases and support on T.
`lem-sc-supported-factor-through-thick` vs `lem-pc-compact-generators-build-objects`: the existing node constructs the telescope, while the new node states the separate Tag 09SP finite-thick-factorization property for maps into a stage.
`lem-sc-supported-factor-through-thick` vs `lem-sc-supported-derived-generated-perfect`: the existing node is a scheme-specific supported-generation statement, while the new node is the generic triangulated-category factorization theorem with a compact source.

`lem-sc-rhom-supported-qcoherent` vs `lem-sc-pseudo-coherent-support-annihilation`: the child supplies the internal-Hom reduction, while the item concludes existence of a perfect annihilator.
`lem-sc-supported-factor-through-thick` vs `lem-sc-pseudo-coherent-support-annihilation`: the child supplies finite-stage factorization, while the item concludes existence of a perfect annihilator.

## Review by K1

I reread `/home/ubuntu/c1-stacks-review/perfect.tex` at Tags 0A6H and 0A9C, `/home/ubuntu/c1-stacks-review/duality.tex` at Tag 0E4G, and `/home/ubuntu/c1-stacks-review/derived.tex` at Tags 09SN, 09SP, and 094A. The item statement agrees with Tag 0A9C: Y is qcqs, V is quasi-compact, T is its closed complement, and the two alternatives have exactly the perfect or pseudo-coherent plus bounded-below hypotheses. The internal-Hom node now cites the correct quasi-coherence lemma 0A6H; its support clause is the restriction argument in 0A9C.

Step 1 uses the internal-Hom statement for quasi-coherence, bounded-below locality, and support, then uses tensor-Hom adjunction as the elementary translation. Step 2 uses the existing supported-generation node for a perfect E supported on T and the existing Tag 094A compact-Hom node to represent the map at a finite stage; their statements include the required D_QCoh, support, coproduct, and compactness hypotheses. Step 3 uses the new Tag 09SP node exactly for a map from compact `O_Y[0]` into that stage. The single-generator specialization is immediate, and closure of perfect complexes and support under finite sums, shifts, cones, and summands gives the stated properties of Q'. Step 4 explicitly checks the distinguished triangle, restriction to V, vanishing of Q' on V, and cone closure. Step 5 is the tensor-Hom adjunction.

For the new node I checked the generic category, arbitrary coproducts, compact generator family, 09SN stage hypotheses, and compact source against Tag 09SP. I searched the whole DAG and blueprint before restoring it; no node states this factorization theorem. The Mathlib leanfinder, loogle, grep, and unavailable leansearch results are recorded exactly in the node. I also checked V=Y and V empty as edge cases. The returned points are repaired by dropping both duplicates, replacing the false finite-stage claim, restoring 09SP, and correcting 0A6H/0A9C source attribution.

## Second reading by K1

- Step 1 checked against perfect.tex Tags 0A9C and 0A6H: the RHom cases, bounded-below condition, support restriction, and tensor-Hom translation are covered; verdict pass.
- Step 2 checked against duality.tex Tag 0E4G, derived.tex Tag 09SN, and Tag 094A: the supported generator sequence and compact finite-stage representation have the required hypotheses; verdict pass.
- Step 3 checked against derived.tex Tag 09SP and the supported-generator node: singleton specialization is valid, and the text now spells out perfectness and support closure; verdict pass.
- Step 4 checked against the triangulated-category definitions and perfect.tex Tag 0A9C: the completion triangle, restriction isomorphism, cone perfectness, and zero composite are valid; verdict pass.
- Step 5 checked against the tensor-Hom adjunction in perfect.tex Tag 0A9C: the adjoint map is exactly the required composite; verdict pass.
- Node lem-sc-rhom-supported-qcoherent checked against perfect.tex Tag 0A6H(1),(2) and the support paragraph of Tag 0A9C, including empty and full opens; verdict pass.
- Node lem-sc-supported-factor-through-thick checked against derived.tex Tag 09SP, including arbitrary coproduct stages, compact source, and finite thick closure; the statement now defines "thick subcategory" and has no tag-dependent meaning; verdict pass.
- Changed the factorization statement to be self-contained and removed its external "as in Tag 09SN" wording.
- Expanded Step 3 to justify support closure under the finite thick operations used there.
- Rechecked the zero object, field, empty scheme, and V=Y/V=empty edge cases; no statement changes were needed.
