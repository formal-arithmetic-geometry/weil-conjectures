## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_mulEquiv_prod_picZero` in
`Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`, with its signature unchanged.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.Curve.Picard`.
The curve hypotheses imply irreducibility and smooth relative dimension one; the source
library then supplies the degree homomorphism, its kernel identification and surjectivity.
The proof constructs the section by integer powers and the product equivalence explicitly,
checking its inverses, multiplicativity, degree coordinate and identity on the kernel.
The DAG proof and proof dependencies now follow this route. No public imports changed.

Searches: LeanFinder for Picard degree splitting returned class-group and elliptic-curve
results, with no match. Loogle for `zpowersHom` found the integer-power homomorphism.
The search service grep returned no match for the source degree names; local `rg` found
`picDegreeHom`, `coe_ker_picDegreeHom`, `surjective_picDegreeHom` and the source splitting
in `Curve/Picard.lean`. The source splitting only promises the first coordinate, so the
required compatibility with the inclusion of Pic-zero is checked in our explicit proof.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.exists_mulEquiv_prod_picZero`
(node `lem-sc-pic-proper-decomposition`): one of one original sorries closed.
No sorry remains in the delivered module; no new theorem or sorry was added.
Local single-file compilation passes without warnings. The source-library dependencies
are used as provided; the delivery dry run checks their transitive axioms.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.DivisorClassCurve`
- `Sheaf.AlgebraicGeometry.DivisorModule`
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
- `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality`
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`

Removed direct proof dependencies `lem-sc-divisor-class-curve`, `def-sc-divisor`,
`lem-sc-smooth-connected-curve-local-rings`, `lem-sc-deg-principal-zero`, and
`lem-weil-pbc-closed-point-residue-field-base`. The full divisor module and divisor-class
comparison are unnecessary for this splitting; the source degree-one closed-point lemma
already supplies its geometric input. Residue-field facts and source Serre duality may
remain transitively imported by the source library; this delivery does not claim those
modules disappear from the global target closure. `PicardFunctor` remains visible via
existing public imports. The unit record `sk-def-pic` has no realized statement or steps
that this route would bypass; the degree-one point and elementary splitting route is kept.

## Where the brief, the DAG or earlier work was wrong

The previous DAG route required substantially more theory than the source library needs
for this statement. Its source candidate was correctly noted to omit compatibility with
the inclusion of Pic-zero, but it is unnecessary to redo the divisor-class comparison:
we can use the source surjectivity theorem and verify that compatibility directly.
The source relative-dimension hypothesis follows from smoothness, regular connected
irreducibility and the existing dimension-one hypothesis. No statement was changed.

## Second reading by N1

1. Compared the delivered Lean module with the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only proof imports and the theorem proof differ. Verdict: pass.

2. Compiled `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` locally with `lcompile.py`. It compiles without errors or warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and has no hollow definitions. Verdict: pass.

3. Checked the proof route and declarations used. The proof uses the source Picard degree homomorphism, kernel-carrier theorem, and surjectivity theorem, then gives an explicit multiplicative splitting and verifies both inverse laws and the Pic-zero restriction. No split-off theorem or new statement was added, so there are no new-node truth or duplication issues. Verdict: pass.

4. Checked pruning and imports against the proof. The removed direct proof imports are unused after the source-library route; the report lists each removed import and corresponding old dependency. The unit route remains the degree-one section followed by the elementary splitting. Verdict: pass.

5. Checked the DAG node against the Lean proof. The node's proof paragraphs, proof dependencies, and proof origin describe the relative-dimension setup, source degree results, and explicit product equivalence used by the theorem; no statement was changed. Verdict: pass.

I changed nothing during second reading.
