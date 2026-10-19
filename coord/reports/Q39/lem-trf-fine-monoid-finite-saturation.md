# Stage 1 report: lem-trf-fine-monoid-finite-saturation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fine-monoid-finite-saturation.json`: item split, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-gordan-rational-cone-finite.json`: statement-only support node, no Mathlib match.
- `citations.json`: verbatim citations for the non-elementary first step.

## Attachments

None. A search of the slopmaster2 Lean source found no declaration tagged `(blueprint: lem-trf-fine-monoid-finite-saturation)` and no sorry-free declaration with the item statement.

## WANTED

None; the ILO PDF is present locally.

## What I checked and corrected

The imported item had no proof. I compared its definitions with ILO Expose VIII 3.1.17 (saturation and localization) and the proof of 3.2.9 (finite toric saturation). The current statement correctly keeps the group completion possibly torsion and asks only for finite module generation; it does not assert the stronger normalization claim in 3.2.9. I searched the full DAG and both blueprint snapshots for Gordan, affine semigroup, finite saturation, and localization compatibility. The only reusable nearby fact is the Mathlib leaf node `lem-trf-fg-torsionfree-group-free`; no duplicate saturation node exists.

Step 1 uses exactly the statements of `lem-trf-fg-torsionfree-group-free` (the torsion-free quotient has a finite basis) and the new Gordan node (finite lattice-point translates in a rational cone). I checked the hypotheses: the quotient of the finitely generated group completion by its finite torsion subgroup is finitely generated and torsion-free, and the image of the chosen finite generators gives the cone. Multiplying by the exponent of the finite torsion subgroup proves both directions of the identification with the root closure; adding all torsion translates to the finite set gives the displayed union.

Step 2 is definitional: a submonoid of the group completion is integral, its group completion is unchanged because it contains P, and the root-closure condition is exactly saturation. Step 3 writes both inclusions for localization explicitly; in the forward direction the witness is `n(x+s)=p+(n-1)s`, and in the reverse direction it is `n(a-s)=na-ns`. Step 4 expands the monoid-algebra basis and the equality `z^(f+p)=z^f z^p`, so the finite translate set gives finite module generators.

I tested the statement on the zero monoid, `P=\\mathbf N`, `P=2\\mathbf N`, `P=\\mathbf N^2`, localization by `S=P`, and a finitely generated monoid in `\\mathbf N\\oplus\\mathbf Z/2`; all edge cases satisfy the displayed clauses. The new support node is strictly more general in geometric form (a lattice cone) and does not restate the item's monoid saturation statement.

## Review by Q39

I reread the item and support-node JSON files and the source passages in the ILO PDF. For Step 1 I verified that both cited node statements actually provide what is used: the existing node supplies a finite basis for the torsion-free quotient, and the new node supplies the finite translate decomposition. I checked the missing torsion hypothesis by passing to `G/T`, multiplying by the finite exponent of `T`, and explicitly adding the finitely many torsion translates. Steps 2 and 3 use only the definitions already introduced by the item and the two inclusions are written out, so they are elementary. Step 4 uses only the displayed monoid-algebra definition and the translate equality, with no hidden ring-theoretic fact. I corrected the initial proof plan to cite the existing torsion-free-group node and added it to `proof_deps` and `citations.json`. The Mathlib searches were run with `msearch.py` for the item and for the new node; all returned only unrelated general localization, semilinear-set, or saturation definitions, so both remain non-Mathlib statements.
