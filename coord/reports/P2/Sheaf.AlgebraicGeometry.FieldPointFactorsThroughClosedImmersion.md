## What changed

Proved `AlgebraicGeometry.field_point_factors_through_closed_immersion` in
`Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion`, with its statement,
universe, and public imports unchanged. All work is in this item's sandbox.

Existence follows the DAG: Mathlib's field-point factorization gives the map from the
residue field at the image point; compose it with the inverse residue-field map of the
closed immersion, then apply Spec and the canonical residue-field point. Residue-field
naturality and contravariant functoriality prove the factorization equation. The equality
between the default point and the closed point uses the singleton spectrum of a field.
Uniqueness uses `cancel_mono i`, since Mathlib already supplies `Mono i` for closed
immersions. Injectivity on points proves the point assertion for every lift.

Updated the docstring and the node's proof/proof_origin to reflect that uniqueness
argument. All six original proof dependencies remain used; no imports were added.
This node does not realize the unit's statement or any entry of its realized steps, and
the unit route is unchanged.

Searches actually run: LeanFinder for field-point factorization through a closed
immersion, Loogle for `Scheme.SpecToEquivOfField`, and ripgrep of the source library,
Sheaf, and Mathlib's closed immersion/preimmersion modules. The exact source signatures
of the field-point factorization, residue-field naturality, and residue-field isomorphism
were read. The relevant Stacks statements were checked at
https://stacks.math.columbia.edu/tag/01J9 and
https://stacks.math.columbia.edu/tag/01L7 (the local literature mirror lacks schemes.tex).

Validation: the module compiled cleanly with `lcompile.py`; the import-direction check
accepted the retained proof import. Delivery dry-run validation is the final check.

## Proved and sorry left

Proved the sole former sorry:
`AlgebraicGeometry.field_point_factors_through_closed_immersion`
(node `lem-weil-pbc-field-point-factors-through-closed-immersion`).
No sorry remains in this module. No new theorem, module, or sorry was introduced.

The proof uses the existing named theorem
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`
(node `lem-weil-pbc-closed-immersion-residue-field-iso`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`), which still contains sorry
in the repository source. It is retained as the next proof dependency, as stage 3 intends.

## No longer needed

None: no imported module or DAG dependency was removed. The second application of the
point-and-field-map bijection in the planned uniqueness proof is unnecessary, but its
node and the naturality node remain needed for existence. Both original imports are
used, and there are no additional modules to prune.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's uniqueness argument can be shortened using
Mathlib's existing monomorphism instance for closed immersions (Stacks Tag 01L7).
The hypothesis on the image point is used only after identifying the default point
with the closed point of Spec K; no assumption on K beyond Field is added.

## Second reading by P2

1. Compared the delivered module with the repository version. The theorem signature,
universe, definitions, and public imports are byte-for-byte unchanged; only the
docstring and proof body changed.
2. Compiled the module with `lcompile.py`; it succeeds with no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the retained
closed-immersion residue-field theorem and permitted kernel axioms.
3. Checked the sole statement and its edge case of a field-valued point at the closed
point. It is unchanged, and no split-off statement or new node was introduced.
4. Reviewed the proof route and imports. Existence uses the residue-field
isomorphism and naturality; uniqueness uses Mathlib's `Mono` instance for closed
immersions, a shorter valid route. No import or dependency can be pruned.
5. Compared the DAG proof, dependencies, origin, and unit metadata with the Lean
proof. They agree; the unit's realized route is untouched.

Changed only this report section and the existing node's proof metadata to record the
shorter cancellation argument; no theorem statement or definition was changed.
