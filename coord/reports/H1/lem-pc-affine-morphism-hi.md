## Files written

- `dag/nodes/sec-picard-framework/lem-pc-affine-morphism-hi.json`: repaired item, two proof steps, no new child nodes.
- `citations.json`: verbatim citations for every proof use.

## Attachments

None.

## WANTED

None.

## What was wrong

The returned version introduced `lem-pc-affine-higher-direct-image-vanishing`, which restated the item's own vanishing conclusion and was therefore a D2 non-split. It also used the finite-support theorem's degree-zero clause without an explicit statement that $R^0f_*=f_*$. I removed the child and replaced both issues with direct existing results.

## What I could not finish

Nothing.

## Review by H1

I read the imported item and its blueprint proof, the higher-direct-image presheaf node, the affine cohomology vanishing node, the affine morphism definition and permanence node, the zero-stalk criterion, and the dedicated qcqs pushforward node. Step 1 now takes exactly the stalk-colimit statement from `lem-weil-pbc-higher-direct-image-presheaf`; affine opens are cofinal by the scheme affine-open basis, their inverse images are affine by `pqf-def-affine-morphism`, and `lem-pc-affine-vanishing` kills each cohomology term. The cited zero-stalk node then supplies the conclusion. Step 2 uses clause (3) of `lem-weil-pbc-affine-morphism-permanence` for the required quasi-compact and quasi-separated hypotheses and applies `pqf-lem-pushforward-qcoh` directly, avoiding any unsupported degree-zero reading of `lem-pc-finite-support-hi`. I checked every quote in `citations.json` verbatim against its node statement, verified that the deleted child is no longer referenced, and retained the blueprint statement unchanged. Small cases (identity affine morphism, empty/zero module, and degree zero) are consistent with the repaired proof.

## Second reading by H1

- Statement: checked against the imported blueprint statement and the Lean declarations `isZero_higherDirectImage_of_isAffineHom` and `isQuasicoherent_pushforward_of_isAffineHom`; the hypotheses and both conclusions agree, including the degree-zero pushforward convention.
- Step 1: checked against Stacks Tags 01E4 (higher-direct-image stalk description) and 01EO (affine cohomology vanishing); the cited presheaf, affine-morphism, vanishing, and zero-stalk statements supply the non-elementary facts, while cofinality of affine neighborhoods is the defining affine-open basis property of schemes. Verdict: sound.
- Step 2: checked against Stacks Tags 01S7/01SD for affine-morphism permanence and 01LC for quasi-coherent pushforward; the cited permanence clause gives quasi-compact and quasi-separated, and the cited pushforward theorem gives exactly the conclusion. Verdict: sound.
- New nodes: none remain; the former higher-direct-image vanishing child was a restatement of the item and was removed.
- Small cases: identity on an affine scheme, empty scheme, zero module, and `i = 0` all satisfy the statement and the two-step proof.
- Changes made: retained the two-step proof and verbatim citations, removed the non-split restatement child, and documented the elementary affine-basis cofinality used in Step 1.
