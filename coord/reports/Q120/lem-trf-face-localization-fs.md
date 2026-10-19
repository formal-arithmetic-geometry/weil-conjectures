# Stage-1 report: lem-trf-face-localization-fs

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-face-localization-fs.json`: split statement with four proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-face-fg.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node and step.

## Attachments

No finished project declaration matched the item. The source tree contains no declaration tagged `(blueprint: lem-trf-face-localization-fs)`.

## WANTED

None. The ILO source is present in `literature/`.

## Not duplicates

- `lem-trf-face-fg` vs `lem-trf-face-localization-fs`: the new node states only finite generation of a face of a fine monoid, while the item proves integrality, saturation, finite generation of the localization, and the group-completion isomorphism.
- `lem-trf-face-fg` vs `lem-trf-face-localization-units`: the new node concerns finite generation of the face itself; the existing node characterizes units after localization and assumes integrality.

## Review by Q120

I read the imported item, its unit and chapter records, and the sharp-chart citer `lem-trf-fs-face-sharpening`. I read ILO Expose VIII §§3.1.1–3.1.2 (printed pp. 98–99), including the definitions of sharpening and localization, and checked the finite-type-face comment after Expose XVI §3.6.5 (printed p. 253). The statement retains the original fine saturated hypotheses and all four conclusions.

Step 1 uses `lem-trf-face-fg`; its statement says exactly that a face of a finitely generated integral monoid is finitely generated. Step 2 uses that node for generators of `F` and `def-trf-fs-log-blowup` for the meaning of fine saturated; the displayed generators `q_i` and `-f_j` prove finite generation, while containment in `Q^{gp}` proves integrality. Step 3 uses the saturation clause of `def-trf-fs-log-blowup` and writes the full calculation `n(x+f)=q+(n-1)f`, so no unstated localization theorem is used. Step 4 uses the group-completion definition from `def-trf-fs-log-blowup`; the two inclusions give injectivity and surjectivity of the canonical map.

I tested the edge cases `F={0}`, `F=Q`, and coordinate faces in `Q=\mathbf N^2`; these cover unchanged localization, the zero quotient case used by the sharpening citer, and a nontrivial face. I searched the whole DAG and blueprint for the face-localization and finite-generation statements and found no duplicate. The new face-finiteness node was searched with LeanFinder, Loogle, LeanSearch, and targeted Mathlib grep; the recorded searches found only generic `Localization.fg`/`AddLocalization.fg` declarations and no face theorem. No Lean code, compiler, Lake, or build tool was used.

## What was wrong or incomplete

The imported item had an empty proof. I added the finite-generation supporting statement and made the remaining algebraic arguments explicit, including the saturation calculation and the group-completion map. No source statement was corrected.

## What remains

The new face-finiteness node is statement-only and awaits later stages. No `sorry` or Lean declaration was written.
