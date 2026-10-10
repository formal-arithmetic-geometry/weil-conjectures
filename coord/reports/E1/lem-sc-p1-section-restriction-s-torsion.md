Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-section-restriction-s-torsion.json` (statement, split)
- No new nodes; the localization kernel criterion is already in `def-weil-pbc-module-localization`.

Attachments: none.

WANTED: none.

The item had no project declaration matching its statement. I checked the parent route and Stacks Properties Lemma 01PW. The proof follows the finite affine trivializing cover used for injectivity: on each affine, quasi-coherence and the affine tilde/localization statements identify restriction to the basic open with module localization; the defining localization criterion already recorded in `def-weil-pbc-module-localization` supplies a power annihilating the local section; finiteness gives one uniform exponent and the sheaf property globalizes the vanishing. I checked the hypotheses used in each step: quasi-compactness gives a finite subcover, invertibility gives local rank-one trivializations, and quasi-coherence gives the affine module description. The imported item-level Mathlib searches were retained and no new node was needed.

## Review by E1

I read the target node, its parent `lem-sc-p1-invertible-section-localization`, and the source route in Properties 01PW. Step 1 uses only the quasi-compact and invertible-module definitions to choose finitely many affine trivializing opens and identify the nonvanishing locus with a basic open. Step 2 uses the exact localization statement of `lem-weil-pbc-spec-module-tilde-sections`, the quasi-coherent affine counit in `lem-weil-pbc-affine-tilde-gamma-adjunction`, and the annihilator clause in `def-weil-pbc-module-localization`; these provide precisely the local module element and its power annihilator. Step 3 takes the maximum of finitely many exponents and applies the local rank-one description plus the sheaf gluing criterion. I also checked small cases: for `s=0`, `X_s` is empty and `m=1` makes multiplication by `s` zero; for `s` a unit, `m=0` works; for `L=O_X` this reduces to ordinary module localization. The algebraic localization fact was not made into a duplicate node because it is already stated by the existing definition.

What I could not finish: no Lean source declaration proves the item itself; this is therefore a natural-language split, as required.

## Second reading by E1

- Item statement: checked against Properties Lemma 01PW (label `lemma-invert-s-sections`), clause (1), with the quasi-compact and quasi-separated hypotheses, invertible module, residue-field nonvanishing locus, and tensor-power conclusion all present; verdict: agrees after adding the explicit quasi-separated definition dependency.
- Step 1: checked against the finite affine trivializing-cover paragraph of 01PW; finite choice follows from quasi-compactness and local rank-one triviality, and the identification with `D(f_i)` is correct; verdict: sound.
- Step 2: checked against the affine localization calculation in 01PW and the statements of `lem-weil-pbc-spec-module-tilde-sections`, `lem-weil-pbc-affine-tilde-gamma-adjunction`, and `def-weil-pbc-module-localization`; verdict: each cited statement supplies the claimed localization or annihilator fact.
- Step 3: checked against the conclusion of 01PW clause (1); the finite maximum and sheafwise vanishing argument are elementary from the stated local equations and invertible-module trivialization; verdict: sound.
- New-node audit: there are no auxiliary new nodes; the item node is a statement-only split, with citations and recorded Mathlib searches checked; verdict: no duplicate or unnecessary child node.
- Edge cases: tested `s=0` (empty nonvanishing locus), `s` a unit (`m=0`), and `\\mathcal L=\\mathcal O_X` (ordinary module localization); all behave as stated.
- Changes: set `created.item` to this delivered item, added `def-weil-quasi-separated-morphism` and an explicit quasi-separated parenthetical to make the statement self-contained, and recorded this second reading.

