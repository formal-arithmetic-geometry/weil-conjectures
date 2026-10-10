1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-closed-immersion-coherent-cohomology.json`, statement, split proof, no Mathlib match.
- No new nodes; the audit's higher-direct-image declaration is attached to existing node `lem-pc-finite-support-hi` (Tag 01XJ).

2. Attachments: `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage` belongs to `lem-pc-finite-support-hi`. The sorry-free declarations `isFinitePresentation_pushforward_of_isClosedImmersion`, `nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`, `isIso_projectionHom`, and `nonempty_pushforward_tensorObj_pullback_iso` are covered by the item proof; no one declaration states all three clauses.

3. WANTED: none.

4. The imported node had `status: imported`, an unfilled blueprint reference, no Mathlib searches, and an open slopmaster2 declaration. I filled the blueprint and split out the missing `isQuasicoherent_higherDirectImage` statement. The proof now explicitly cites that child for quasi-coherence, the existing affine higher-image node for vanishing, and the existing Leray and invertibility nodes. I checked the child against `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean:467-474` and the parent declarations in `ClosedImmersion.lean`, `Affine.lean`, and `ProjectionFormula.lean`.

## Review by E1

I read the blueprint proof and the source declarations. Step 1 uses finite generation on affine charts for coherence, existing node `lem-pc-finite-support-hi` for quasi-coherence of higher direct images, the affine-morphism higher-image statement for vanishing, Leray for the cohomology comparison, and the invertible-module definition for local trivialization. The hypotheses are checked: a closed immersion is affine, the source and target are locally Noetherian, and the sheaf is coherent hence quasi-coherent. The tensor assertion is checked on a trivializing open cover and glued by naturality. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item; LeanSearch was unavailable and recorded as such. I tested the empty immersion and identity immersion as edge cases. The apparent new child was removed after reading `lem-pc-finite-support-hi`, which already states the same Tag 01XJ fact.

## Second reading by E1

- Item statement: checked against the blueprint node and the sorry-free slopmaster2 declarations for closed-immersion finite presentation, affine cohomology, and projection formula; all three clauses and all hypotheses agree.
- Step 1: checked the affine quotient calculation on $V=\operatorname{Spec}(R)$ against the closed-immersion module declaration and `pqf-lem-coherent-ft-locnoeth`; the localization argument supplies finite type and quasi-coherence.
- Step 1: checked `lem-pc-finite-support-hi` for quasi-coherence of higher direct images, `lem-pc-affine-morphism-hi` for affine higher-image vanishing, and `pqf-lem-leray` for the single-row cohomology comparison; each cited statement says exactly what is used.
- Step 1: checked the tensor clause against `def-sc-invertible-module`; local generators identify both sides with the pushforward and the natural map, so the local isomorphisms glue.
- New nodes: none; the apparent higher-direct-image helper was correctly omitted because `lem-pc-finite-support-hi` already states the needed Tag 01XJ result. Existing-node searches covered the coherence, affine, Leray, and invertibility facts.
- Edge cases checked: the empty closed immersion, the identity immersion, a field-valued affine scheme, and degrees $q=0,1$; all clauses reduce correctly.
- Changes made: no mathematical statement or dependency was changed; this second reading records the source, hypotheses, cited statements, duplicate-node decision, and edge-case checks.
