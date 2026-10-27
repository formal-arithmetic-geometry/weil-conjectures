# Q151 stage-1 delivery: lem-sfb-local-split-root-data-weyl-lifts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-split-root-data-weyl-lifts.json: item, split in seven steps, original statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-tangent-weight-base-change.json: new statement, unsplit, no Mathlib match. General smooth affine group tangent module, full torus coaction and arbitrary base change.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-canonical-root-exponential.json: new statement, unsplit, no Mathlib match. Canonical closed root-line map without choosing a global basis, including uniqueness.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-opposite-root-reflection-map.json: new statement, unsplit, no Mathlib match. Perfect opposite-root pairing, relative coroot and explicit three-exponential rank-one normalizer formula.
- citations.json records the verbatim statements used by each proof step; searches.jsonl retains the twelve actual search results. No Lean files were written or compiled.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, reductivity, root subgroups and Weyl terminology found no declaration stating the item. The Lie-algebra reductivity declarations there are characteristic-zero Lie-algebra results, with different objects and conclusions. General dual-number tangent files cover fields or tangent operations, not the relative root and Weyl assertions here.

## Literature wanted

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, introduction to Section 4 p.107, Theorem 4.1.4 p.110 and proof pp.116-118, Theorem 4.2.6 pp.120-121, Definition 5.1.1 and discussion p.136, Proposition 5.1.6 p.138, Corollary 5.1.9 pp.140-142 and Corollary 5.1.11 pp.142-143; for the item and all three new nodes. Desired local path: literature/conrad-reductive-group-schemes.pdf. I read the author's online PDF but it is absent from the literature catalogue; I did not download or write outside the sandbox. Accordingly proof_origin.by is agent. The source is Conrad, with no SGA source cited as a proof route.

I also read literature/stacks-project/algebra.tex, lemma-finite-projective, Tag 00NX (tags/tags confirms the label), to check the existing finite-projective standard-open lemma actually supplies the localization used at the maximal ideal.

## Problems and corrections

No mathematical statement dispute was found and no hypothesis or conclusion of the item was changed. The imported item had no proof. The source's global split definition includes root-line freeness, so applying its global Weyl-lifting corollary without first proving that freeness would leave a gap. Step 1 proves it at the unique maximal ideal, then uses fibre dimensions to identify all the roots. The explicit rank-one maps then give the lifts, rather than assuming fibre points lift through the normalizer.

The item has blueprint.from.node = null. The required ancestor command also returns None; its existing created.item chain is broken above lem-sfb-admissible-direct-image. I preserved that computed value and the full existing via chain, and gave every new node the required via chain with this item prepended. All from.place values name the inherited direct-image/alteration prerequisite and the specific source fact. I read the current literature/blueprint/latest direct-images statement and proof: this remains the supporting relative-root prerequisite on its existing alteration branch, with no replacement of the unit's direct-image route. Whole-blueprint searches for root subgroup, normalizer, weight torus, root datum, exponential group and coroot found no applicable blueprint statement. The root-datum search returned unrelated coefficient/Weil-root uses, which were not matches. same_as is empty.

## Not duplicates

lem-sfb-relative-tangent-weight-base-change vs lem-sfb-trivial-torus-coherent-weight-decomposition: the existing node assumes a scheme over a field and a coherent linearization; the new node constructs the tangent module and coaction of a smooth group over an arbitrary Noetherian ring and compares it under arbitrary algebra base change. The existing statement does not supply the relative tangent comparison.

lem-sfb-relative-canonical-root-exponential vs lem-sfb-reductive-root-subgroup-parametrizations: the existing node is over an algebraically closed field. The new theorem constructs a canonical map from a possibly nontrivial root line over a ring, uniquely specified by its tangent map, with arbitrary base change. This uniqueness is used for conjugation over nilpotent bases, which a fibre assertion alone cannot establish.

lem-sfb-relative-opposite-root-reflection-map vs lem-sfb-reductive-rank-one-reflections: the existing statement is over an algebraically closed field and gives a rank-one SL2 map and root reflection. The new node constructs the pairing and three-exponential normalizer element over a base ring, even without free global root modules or globally constant roots. It does not assert existence of representatives for the entire Weyl group.

lem-sfb-relative-opposite-root-reflection-map vs lem-sfb-opposite-root-sl2-parametrizations: the existing node gives field-valued rank-one SL2 parametrizations; it cannot supply the relative pairing or a normalizer element over the original local ring.

None of these nodes restates the entire item or merely packages its output clauses. Step 1 supplies the local freeness and constancy argument; step 2 constructs the regular functional; step 3 chooses actual additive parametrizations; step 4 writes the monomial rigidity calculation; steps 5 and 6 construct all Weyl lifts from rank-one generators and prove the fibre identification; step 7 proves relative subgroup conjugation by uniqueness. Each new prerequisite is a general relative structural statement strictly smaller than this assembled local result. None is an elementary two-line specialization of an existing node. No new source has a Stacks tag overlapping the item or another node; the 00NX input is reused directly.

## Review by Q151

I read delivery-errors B through E in full and checked this split against their mathematical requirements, not only its JSON form. I read Conrad's Section 4 introduction and Definition 5.1.1 discussion for the root-module and constant-lattice issues, Theorem 4.1.4 and its dynamic proof for the canonical exponential, Theorem 4.2.6 and Corollary 5.1.9 for the pairing and reflection, and the proof of Corollary 5.1.11 for generation of all representatives. I did not cite a field theorem to obtain a group element over A. The three new statements have their own bases, groups, torus, characters, tangent modules and group laws specified; their proofs remain empty because this is a one-level split.

Step 1 uses exactly the new tangent theorem's finite projectivity, finite weight support and scalar-extension comparison, the existing prime-local-free theorem's actual standard-open conclusion, and the field rank-one theorem's one-dimensional nonzero weights and opposite-root assertion. The localization element lies outside the unique maximal ideal and is therefore a unit. A zero fibre dimension is used only after the module has become free, so no unstated Nakayama or geometric reducedness inference is hidden. All fields considered are geometric A-fields; the reductivity and maximality hypotheses are exactly the item's geometric assumptions.

Step 2 is the elementary polynomial choice of an integer outside finitely many root sets, and requires only that the finite root vectors are nonzero. It does not assume the roots span M. Step 3 uses the canonical exponential theorem's actual closed-image, equivariance and base-change assertions; precomposing with the chosen rank-one basis is explicit. Step 4 is a direct coefficient check in the Laurent basis: idempotents, their orthogonality and their sum prove monomial rigidity even over a nonreduced local ring. It creates no extra lemma node because the proof is written out in a few lines.

Step 5 invokes the new opposite-root theorem only for the two root lines already known free. Perfectness gives the dual element Y, and the three-exponential formula gives an A-point of the normalizer. The reflection convention is checked using c_alpha(alpha)=2, so the inverse action in the character convention has the same reflection. The local group-like calculation proves that the coroot is a fixed integer vector, independent of geometric fibre.

Step 6 uses the opened statements of lem-sfb-weyl-reflection-realization and lem-sfb-reductive-borel-pair-structure. The former asserts injectivity only on the rational root span, so I explicitly pass from a word agreeing on that span to equality in the normalizer quotient. This gives the full M-action without claiming that the root span equals M tensor Q. The Borel required by that existing statement is supplied by the latter node for each algebraically closed fibre. Word products give n_w over A; the maps to the fibre quotients are group isomorphisms even though no group section into H(A) is asserted. Empty roots are covered by injectivity on the zero space.

Step 7 uses the full relative uniqueness of the exponential, not just equality of geometric fibres. The displayed differentiated conjugation formula proves which weight line maps to which, and the transported exponential has exactly the tangent inclusion required by the uniqueness statement. Arbitrary successive base-change compatibility is explicitly in the tangent and exponential statements, so the final field-extension assertion is justified by those statements and the fixed word products.

Small cases checked: r=0 gives M=0, empty roots and trivial W; an arbitrary split torus has empty roots but may have positive r; SL2 has roots twice the basic torus character, including in characteristic 2, where differentiated characters cannot be used; the coaction formulation retains them. Over a nonreduced local ring such as F_2[delta]/(delta^2), group-like Laurent coefficients are still idempotents, and root-line freeness uses local projectivity rather than reducedness. Reductivity is required on every geometric fibre, not only the closed fibre. The new exponential needs a rank-one root module everywhere and therefore does not purport to attach a subgroup to a weight that disappears on part of a disconnected base. The rank-one formula needs a generator only where it is evaluated, while its pairing and coroot are global.

All seven steps have fewer than 2000 characters. I checked no step hides an additional non-elementary comparison, extension-of-fields result, existence of a normalizer lift, or group generation assertion beyond its citations. citations.json contains one verbatim witness for each use. The only off-unit tool is finite-projective prime-local freeness; it is declared in split_report.tool_uses with the precise specialization. No maintainer review, unit record, Lean record, or source repository file was edited.

## Unfinished work

The three new prerequisites are intentionally statement-only nodes for later splitting. Nothing in the assigned one-level split remains unfinished; delivery validation follows below.
