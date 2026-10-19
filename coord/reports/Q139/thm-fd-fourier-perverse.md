# Worker report: thm-fd-fourier-perverse

## Files written

- `dag/nodes/sec-deligne-laumon-a1/thm-fd-fourier-perverse.json`: repaired the retained split; no new DAG nodes and no Mathlib leaves.
- `citations.json`: rebuilt with a verbatim statement quote for every cited node in every proof step.

## Attachments

None. The two `slopmaster2` Fourier declarations are finite-coefficient wrappers and are not exact attachments to this bounded constructible `\overline{\mathbf Q}_\ell` statement; their proofs also depend on sorried operation lemmas.

## WANTED

None.

## Findings and corrections

The returned version's step 4 tried to obtain a `\overline{\mathbf Q}_\ell` shift isomorphism by shifting a Roos triangle. That did not establish a compatible morphism of the reduction towers, and it used the smooth-purity model `def-weil-integral-rational-qbar-compact-support` without identifying it with the item's PBC pair category. I removed that argument.

The repaired step 4 first uses `lem-fd-base-change` to bind the `p_{2,!}` in `def-fd-transform` to the adic compact-support operation. It then uses `lem-cbc-integral-compact-support-uniform-restriction` and the exact-functor shift clause of `def-weil-triangulated-category` at the integral stage. `prop-weil-pbc-rational-transport` transports this comparison to finite rational stages, while `lem-cbc-rational-compact-support-coefficient-coherence` states that the comparisons commute with shifts and scalar-extension maps. Thus the shifted maps are natural in the input and compatible with every reduction/restriction transition. `def-weil-pbc-qbar-category` then assembles the compatible finite-stage maps into the common-stage Qlbar isomorphism. This directly repairs E5 and avoids the non-functorial derived-limit uniqueness argument.

Step 5 now binds the affine map and coefficients explicitly: it is the affine relative-dimension-one projection in the adic common-stage category, so `lem-per-artin-gabber-affine-curve` applies to the same `p_{2,!}` used by the transform. This repairs E6/E4's model ambiguity. The statement and all other steps remain unchanged, including the corrected explanation that `[-1]` raises the perverse index in step 2.

## Review by Q139

I reread the current item, the main-20261015 statement and proof, and the statements of every node cited after the repair. The item's statement is unchanged and still agrees word for word with `literature/blueprint/master/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/thm-fd-fourier-perverse.md`; the repaired proof follows the corresponding paragraph of `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/thm-fd-fourier-perverse.proof.md` while making its coefficient passage explicit.

1. Step 1 uses `def-sbc-affine-space`, `sbc-lem-affine-space-smooth`, `def-sbc-smooth-morphisms`, and `def-weil-pbc-scheme-conventions`. Their statements give the two relative affine lines, smoothness and pure relative dimension one, and the separated finite-type hypotheses. The coordinate calculation verifies affine and finite type, and the difference of fiber coordinates verifies the relative diagonals. I checked these over geometric points and over `k_0`.
2. Step 2 uses the two inclusions in `lem-per-smooth-pullback-t-exact` with `d=1` and the shift convention in `def-per-perverse-subcategories`. Both support and cosupport signs were checked: undoing `[1]` gives index `1`, so `[-1]` raises the index.
3. Step 3 uses the statement of `prop-kernel-lisse` for rank one and finite Tor amplitude, `sbc-lem-affine-space-smooth` for smooth pure dimension two of `X`, and the shifted assertions in `lem-per-lisse-tensor-permanence`. The cited statements are in the Qlbar PBC category and no finite-coefficient identification is smuggled in.
4. The repaired step 4 uses the exact integral compact-support functor stated by `lem-cbc-integral-compact-support-uniform-restriction`; `def-weil-triangulated-category` supplies what exactness means, including the shift comparison. `prop-weil-pbc-rational-transport` states the rational extension and its localized shift comparison. `lem-cbc-rational-compact-support-coefficient-coherence` explicitly says the rational compact-support comparisons commute with shifts and scalar-extension cocycles. `def-weil-pbc-qbar-category` states that Qlbar objects and morphisms are represented at finite stages and that shifts are stagewise, so the compatible finite-stage maps form the required common-stage isomorphism. `lem-fd-base-change` supplies the coefficient-model binding for `p_{2,!}`. This checks the reduction maps, restriction of scalars, scalar extensions, and common-stage passage that the returned proof lacked.
5. Step 5 uses the perverse shift definition, `lem-fd-base-change` for the adic meaning of the affine projection, `lem-per-artin-gabber-affine-curve` with `d=1`, and `def-fd-transform` for the rank-one normalization `[1]`. The projection is affine with one-dimensional fibers by step 1, and the output shift is exactly the comparison from step 4. The two signs give the upper and lower bounds separately.
6. Step 6 is the elementary intersection in `def-per-perverse-subcategories`; it does not assume truncation functors or a t-structure.

I checked the small cases `K=0`, the punctual object `\delta_0`, and the constant lisse object `\overline{\mathbf Q}_\ell[1]`; the bounds and the shift comparison are consistent. I also checked the empty-fiber/zero-output case and the rank-one relative dimension. No step exceeds 2000 characters or hides an additional lemma. The proof dependencies are exactly the union of the step uses. There are no new nodes, hence no duplicate or Mathlib-leaf split to review, and the retained Mathlib searches remain unchanged. No SGA source, Lean file, compiler, Lake, or live project file was used.

## Unfinished work

None in this one-level stage-1 split. The cited operation and perverse lemmas remain separate DAG work items; this item does not claim to close their Lean sorry dependencies.
