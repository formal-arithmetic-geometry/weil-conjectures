1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-free-prime-membership.json`: item split, one coordinatewise proof step.
- `citations.json`: exact statement quotes for both cited nodes.

2. Attachments

None. No declaration tagged `(blueprint: lem-sc-free-prime-membership)` or matching the statement was found in `~/weil-conjectures-slopmaster2/WeilConjectures` or `Comparator`.

3. WANTED

None. The source is the locally cited Stacks algebra material (Tag 00NX and the prime-localization construction); the checkout's TeX sources are not present in this repository.

4. What was checked and corrected

The target statement was read together with its blueprint ancestor `lem-sc-pic-proper-ntorsion`; its hypotheses and notation are unchanged. I searched the complete DAG and blueprint for the scalar localization criterion and found no existing node. I also searched the Lean source for the item id, its key phrases, and possible declaration names; no matching declaration exists.

The proof now carries the scalar denominator argument directly: `a/1` lies in the extended prime ideal exactly when some denominator outside the prime multiplies `a` into the prime, and primality gives the converse. This avoids introducing a statement-only child while keeping the step strictly smaller than the item. Small cases checked: `a=0` and `a=1`; for `R=Z`, `p=(2)`, the criterion gives the usual membership in `2 Z_(2)`.

## Review by G1

I read the item source place (Stacks Algebra Tag 00NX, the free-module coordinate calculation) and the statements of `def-weil-pbc-module-localization` and `def-weil-pbc-localization-at-prime`. Step 1 uses the module-localization statement for the canonical map and coordinatewise localization, and the prime-localization statement for the fraction relation and maximal ideal. The denominator/primality argument and the equivalence between coordinatewise membership in `p R^n` and membership in `pF` are written explicitly; the step is marked non-elementary because it uses the prime-localization construction.

I checked the hypotheses at the edge cases `n=0`, `n=1`, `s=0`, and `R=Z, p=(2), s=(2,3)`. The blueprint ancestor and `from.place` identify the affine section translation being realized; the blueprint search found no `same_as` node. I corrected the initial empty proof by adding the scalar child, a complete coordinate argument, proof dependencies, exact citation quotes, and the required search records.

5. What could not be finished

Nothing.
