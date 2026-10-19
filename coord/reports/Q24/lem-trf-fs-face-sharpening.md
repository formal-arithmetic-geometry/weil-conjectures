# Stage-1 report: lem-trf-fs-face-sharpening

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fs-face-sharpening.json`: split statement with six proof steps.
- `lem-trf-face-localization-fs`: statement node, Mathlib search no match.
- `lem-trf-face-localization-units`: statement node, Mathlib search no match.
- `lem-trf-face-subgroup-saturated`: statement node, Mathlib search no match.
- `lem-trf-fg-torsionfree-group-free`: Mathlib leaf matching `Module.basisOfFiniteTypeTorsionFree'`.
- `citations.json`: verbatim statement quotes for every cited node and step.

## Attachments

No finished project declaration matched the item. The source tree contains no declaration tagged `(blueprint: lem-trf-fs-face-sharpening)`.

## WANTED

None. The ILO source is present in `literature/`.

## Not duplicates

- `lem-trf-face-localization-fs` vs `lem-trf-face-localization-units`: the first proves fs localization and group-completion identification; the second characterizes the units after localization.
- `lem-trf-face-subgroup-saturated` vs `lem-trf-face-localization-units`: saturation of the face subgroup is a statement about the quotient group and is independent of the unit characterization.
- `lem-trf-fg-torsionfree-group-free` vs `lem-weil-subgroup-finite-free-abelian-group-free`: the new Mathlib leaf applies to every finitely generated torsion-free abelian group, while the existing node applies to a subgroup of a specified finite free group.

## Review by Q24

I read the imported item and the sharp-chart source node `lem-trf-log-regular-sharp-chart`, including its use of the face localization in proof steps 1--4. I read ILO Expose VIII §§3.1.1--3.1.5 (printed pp. 98--99) for localization, sharpening, and the face-unit calculation, and Expose VI §1.6 and §3.7(a) (printed pp. 70 and 75) for sharp fs characteristics and finite torsion-free group bases. The item statement retains every hypothesis and conclusion of those passages.

Step 1 uses `lem-trf-face-localization-fs`; its statement gives exactly that the localization is integral, finitely generated, saturated, and has group completion `Q^gp`. Step 2 uses `lem-trf-face-localization-units`; its statement says the unit group is exactly `F^gp`, which makes the quotient sharp. Step 3 uses both statements to check finite generation, integrality and saturation after quotienting by units; the lifting argument is written in the step. Step 4 uses both statements to verify injectivity of the canonical map and the group-completion identification. Step 5 uses `lem-trf-face-subgroup-saturated` for torsion-freeness of the quotient and the localization node for finite generation. Step 6 uses the Mathlib leaf, whose declaration `Module.basisOfFiniteTypeTorsionFree'` returns a basis indexed by `Fin r`.

I checked the small cases `F={0}` (so `Q_F=Q` and `R=Q`), `F=Q` (so the quotient is the zero sharp monoid), and `Q=\mathbf N^2` with either coordinate face. These test the unit formula, injectivity, sharpness, and rank-zero edge case. The four new nodes were searched in LeanFinder/LeanSearch, Loogle and Mathlib grep using the recorded queries; only the finite torsion-free group leaf matched. No existing DAG node states any of the three face-specific lemmas, and the duplicate check is recorded above.

The imported item had no proof and status `unsplit`; I added the six explicit steps, their source places, proof dependencies, blueprint ancestry, and verbatim citation quotes. No source statement was corrected.

## What was wrong or incomplete

The imported node had an empty proof and did not distinguish the localization, unit, saturated-subgroup, and finite-basis inputs. Those are now separate nodes, while quotient sharpness and the canonical group map remain explicit steps of the item rather than restated child nodes.

## What remains

The three non-Mathlib child nodes are statement-only and await later stages. No Lean code or compiler was used.
