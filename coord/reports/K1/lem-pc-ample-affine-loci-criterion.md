Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ample-affine-loci-criterion.json` — statement, 4 proof steps, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-complete-linear-system-closed.json` — statement-only unsplit bridge node, no Mathlib match.

Attachments:

- None. The slopmaster2 search found no sorry-free declaration stating the item exactly.

WANTED:

- None.

What was wrong or incomplete:

- The imported item had no proof split. Its source route uses the affine nonvanishing-locus criterion (Properties 01PS), the affine-base construction (Morphisms 01VT), properness of the resulting immersion, and the final complete-linear-system argument in Properties 01Q3. I added those steps and made the cross-unit 01VT theorem an explicit generic tool use. The final projection argument is recorded as the smaller unsplit node `lem-pc-complete-linear-system-closed` rather than hidden in an elementary step.
- No statement was changed. No source error was found.

What I could not finish:

- Nothing.

## Review by K1

I read the item source references in Properties Definition 01PS and Proposition 01Q3, and Morphisms Lemmas 01VT and 01W6 (with Schemes Lemma 01IQ). The item statement agrees with the affine nonvanishing-locus characterization of ampleness for a proper scheme over a field and with the projective closed-immersion meaning of `def-sc-ample`; the hypotheses that $X$ is proper, $\mathcal L$ is invertible, and each stated locus is affine were retained exactly.

Step 1 uses the statement of `def-weil-pbc-ample-invertible-module`: properness supplies quasi-compactness, while the item's affine-locus hypothesis supplies its second condition. This is a direct definition check, with the finite-type/proper convention verified from `def-weil-proper-morphism`.

Step 2 uses `lem-weil-pbc-ample-very-ample-immersion-affine-base`, specialized to the affine base $\operatorname{Spec}(k)$, exactly as Morphisms 01VT (1) implies (5). Its statement supplies a positive tensor power, an immersion into projective space, and the pullback identification. The field case is the projective-space convention used by `def-sc-ample`.

Step 3 uses `lem-weil-pbc-proper-to-separated` for the projective target's separated structure morphism and `lem-weil-pbc-proper-immersion-closed` to turn the resulting proper immersion into a closed immersion. I checked that the properness hypothesis is the original structure morphism $X\to\operatorname{Spec}(k)$ and that the target is projective space over the same field.

Step 4 follows the final paragraph of Properties 01Q3: extend the finite defining sections to a basis, compare the complete-system map with the finite subsystem by linear projection on the nonvanishing open, then use properness and closed image to obtain a closed immersion. The new node `lem-pc-complete-linear-system-closed` states precisely this bridge and is intentionally unsplit. I tested the statement on a point, the empty proper scheme, and $\mathbf P^1$ with $\mathcal O(1)$; in each case the complete-system map has the claimed closed-immersion behavior.

I searched the DAG and blueprint for duplicate statements and searched the Lean source for the item id, its key phrases, and the relevant `IsAmple` declarations. The only related Lean declaration, `AlgebraicGeometry.IsVeryAmple.pullback_of_field`, still has `sorry`; no exact sorry-free attachment exists. Mathlib searches for the new bridge and the item used LeanSearch, LeanFinder, and Mathlib-source grep, all finding no ampleness or complete-linear-system theorem. The DAG checker and split review were run on the complete imported graph; their reported unreachable and pre-existing route diagnostics concern unrelated nodes.
