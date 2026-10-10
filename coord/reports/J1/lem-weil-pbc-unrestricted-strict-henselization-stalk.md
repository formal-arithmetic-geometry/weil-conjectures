# Stage-1 report

Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-unrestricted-strict-henselization-stalk.json`: item split with three proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-cohomology-continuity-unrestricted.json`: one statement-only child, no Mathlib match.
- `citations.json`: verbatim citations for every dependency used by every step.

Attachments: none. No sorry-free project declaration states the unrestricted item. The existing torsion-only proposition is not an attachment.

WANTED: none. The source is Stacks Project Tag 03Q9 in `literature/stacks-project/etale-cohomology.tex` as recorded by the project citation table.

The prior attempt had the child marked as created by another item and left the item metadata inconsistent. I corrected `created.item`, the unit, added the missing pointed-neighbourhood dependency and citation, and kept the proof on the Tag 03Q9 route. The unrestricted continuity child is strictly more general than the existing torsion continuity node, so it is not a duplicate.

## Review by J1

I read the item and the blueprint ancestor `prop-weil-pbc-strict-henselization-stalk-formula`, then checked the Tag 03Q9 proof in the Stacks etale-cohomology source. Step 1 uses the existing 03Q8 higher-direct-image presheaf statement, the geometric-stalk definition, the pointed-etale-neighbourhood definition, and the sheafification-stalk isomorphism; these give exactly the sheafified presheaf and its stalk colimit. Step 2 uses affine cofinality, the strict-henselization limit definition, and the fibre-product-limit lemma; the qcqs hypotheses are retained under the stated base changes and affine transitions. Step 3 uses the new arbitrary-abelian continuity statement and inverse-image definition, yielding the displayed canonical restriction map. Every quoted citation was copied from the cited node statement. I tested the identity system, the zero sheaf, and degree zero: each reduces to the ordinary sections or identity comparison. The child is statement-only, introduces its system, sheaves, limit, cohomology, and canonical map, and records all four required Mathlib searches, with LeanSearch correctly marked unavailable.

## Not duplicates

- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lemma-weil-pbc-etale-cohomology-continuity`: the new child allows arbitrary abelian sheaves, while the existing node assumes torsion sheaves and is therefore insufficient for this item.
- `lem-weil-pbc-unrestricted-strict-henselization-stalk` vs `prop-weil-pbc-strict-henselization-stalk-formula`: the item is the ordinary abelian-sheaf comparison only; the existing proposition has a torsion hypothesis and an additional derived-complex clause.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-unrestricted-strict-henselization-stalk`: the child is the general inverse-system continuity input, while the item is the resulting stalk comparison for one strict henselization.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `prop-weil-pbc-strict-henselization-stalk-formula`: the child proves unrestricted continuity; the existing proposition proves a torsion stalk formula and a separate derived statement.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-integral-cover-kills-constant-cohomology`: the new child is continuity for arbitrary abelian sheaves over inverse systems; the existing node is a finite-cover annihilation statement for constant integral coefficients.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-etale-cohomology-local-ring-colimit`: the new child concerns arbitrary qcqs scheme limits and all degrees; the existing node concerns a local-ring colimit comparison with its own local hypotheses.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-sets-pushforward-stalk-strict-henselization`: the new child is higher cohomology of abelian sheaves; the existing node is degree-zero pushforward for sheaves of sets.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-gm-pullback-strict-henselization`: the new child compares cohomology across an inverse system; the existing node identifies the pullback of the units sheaf on one strict-henselization base change.
- `lem-weil-pbc-etale-cohomology-continuity-unrestricted` vs `lem-weil-pbc-gm-strict-henselization-stalk-formula`: the new child is arbitrary abelian-sheaf continuity, while the existing node specializes the strict-henselization stalk formula to $\\mathbf G_m$ and includes a units identification.

## Second reading by J1

- Item statement: checked against Stacks Tag 03Q9, theorem-higher-direct-images, first assertion; all hypotheses and the canonical map agree, including qcqs, geometric point, strict henselization, and every $q\\geq0$.
- Step 1: checked against Tag 03Q9's first displayed stalk-colimit equality and the cited higher-direct-image, geometric-stalk, pointed-neighbourhood, and sheafification-stalk statements; each citation supplies the stated identification.
- Step 2: checked against Tag 03Q9's affine-neighbourhood and limit paragraph and the cited cofinality, strict-henselization-limit, fibre-product-limit, and qcqs definitions; base changes remain qcqs and affine transitions are justified.
- Step 3: checked against Tag 03Q9's continuity paragraph and Lemma Tag 03Q6; the repaired step explicitly chooses an affine pointed base neighbourhood and a cofinal subsystem, so the continuity child's fixed sheaf and index are instantiated.
- New node `lem-weil-pbc-etale-cohomology-continuity-unrestricted`: checked against Lemma Tag 03Q6 hypothesis by hypothesis; repaired the previously undefined “fixed sheaf” by naming $i_0$, $G_{i_0}$, pullbacks, and the indexing category, and added the inverse-image definition dependency.
- No Mathlib leaf was introduced; the recorded four searches were rerun in the worker split and remain accurate (LeanSearch unavailable).
- Small cases checked: identity inverse system, zero sheaf, and $q=0$ reduce to the identity/ordinary sections comparison.
- Changes made: repaired the continuity child statement and source label, repaired Step 3 to specify the cofinal subsystem and base sheaf, updated the verbatim citation, and recorded this audit.
