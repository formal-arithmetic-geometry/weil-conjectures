## What changed

Started from the current repository version, rather than the stale earlier sandbox.
C4-C7 have already been reduced there. Closed the remaining two bundled statements
`AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero` and
`AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP` by assembling the
connected C1-C8 calculations explicitly, handling the exceptional torsion cases
with the existing primary/nonunit lemmas, constructing the finite clopen connected
component cover, and applying a new component assembly theorem.

Added proof-only imports of `Sheaf.AlgebraicGeometry.Curve.ClopenConstantAssertions`,
`Sheaf.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases`, and
`Sheaf.AlgebraicGeometry.Curve.PrimeTorsionNonunitCohomology`. Added the two proved
private helpers `assertions_constantModSheaf_connected` and
`assertions_constantModSheaf_smooth`. Existing signatures, visibility, and definitions
are unchanged. Updated the two bundled statement nodes to match this proof route.

## Proved and sorry left

Closed both holes of the current baseline (2 of 2):
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero`
  (node `lemma-weil-pbc-smooth-curve-kummer-localization`).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP`
  (node `lemma-weil-pbc-smooth-curve-artin-schreier`).

No sorry remains in the item's module. One new hole is split off:
`AlgebraicGeometry.IsCurve.assertions_constant_of_isClopen`, node
`lem-pbc-k2-clopen-constant-assertions`, in
`Sheaf.AlgebraicGeometry.Curve.ClopenConstantAssertions`.
This is a decomposition, not an axiom-free proof of the bundled assertions:
it closes two upper holes and adds one lower hole (net one). The new statement
is the finite disjoint union step only. It assumes an explicit clopen partition
and supplied assertions for its pieces; it does not supply any curve calculation.
The connected calculation and its eight-field combination are proved in the item.

The complete two-file set compiles through lcompile.py. The independent second
reader should confirm the component assembly statement and run the final dry run.

## No longer needed

Removed the duplicate occurrences (not the last imports) of
`Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeZero`,
`Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne`, and
`Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher`.
No actual dependency module was pruned: those three are still used by C7.

The bundled Kummer node no longer needs its direct proof dependency `def-br`:
Brauer/Kummer inputs remain below the existing connected calculations. All eight
C1-C8 nodes and `thm-sc-main`, realizing the unit's curve calculation step,
remain in this module. No unit statement or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox was stale and its claim that arbitrary coefficients blocked
C4-C7 was superseded by the current repository proofs. The two original bundled
nodes contained long prose but did not name the connected calculations or the
finite disjoint-union assembly step as proof dependencies. This delivery exposes
that step and makes the rest of the reduction Lean.

Edge cases checked: an empty component family forces the empty scheme; one piece
is identity descent; zero modules and the zero ring give zero cohomology;
zero-dimensional connected components satisfy IsCurve and are covered by the
existing connected calculations. Different-primary and noninvertible-prime
cases use zero-object lemmas and never assume Λ/rΛ is nonzero.

The initial launcher dry run hit an environment mismatch: this clone's
`tools/import_cycles.py` lacked the `refuse_missing` and `source_roots` helpers
expected by the deployed `deliver3.py`, so it stopped before compilation. A
compatible current `import_cycles.py` from the project tool set was supplied via
`PYTHONPATH` (no project tool was edited); the required dry run then completed as
`OK (dry run): commit 16e0c7db55 compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.`

## New nodes

`lem-pbc-k2-clopen-constant-assertions` states only finite clopen assembly for a
constant module, with explicit local assertion hypotheses. Its source is the
first paragraph of the blueprint Kummer calculation. Its docstring and DAG node
contain the complete product-of-sites argument, including naturality of the
comparison maps and the conditional assertion hypotheses. It is strictly the
initial reduction step, independent of smoothness and the prime calculations.
The proof plan uses the existing clopen sheaf-product equivalence and
`finiteCoproductCohomologyAssembly`, rather than postponing those identifications
again. The remaining glue is the conditional assertion hypotheses and naturality
of all field-extension/open-restriction maps. These are generic tools already proved
in the library, used below the preserved unit route. No statement/definition change
records or forced adaptations are needed.

## Second reading by K2

1. **No accidental interface changes — PASS.** Compared `SmoothCalculations.lean` with the repository version. Existing declaration signatures and definitions are unchanged; the two target proofs only replace `sorry`. The added `ClopenConstantAssertions` module is a new split-off theorem, and its node records the new statement.

2. **Proof and axioms — PASS.** Compiled both sandbox modules with `lcompile.py --all`; no errors or warnings were reported. The delivered item has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The sole remaining `sorry` is the named public assembly theorem, documented and represented by `lem-pbc-k2-clopen-constant-assertions`.

3. **Statements and split — PASS.** The clopen assembly statement is a true finite disjoint clopen decomposition principle, strictly below the two bundled curve calculations. Its hypotheses are explicit and its conclusion is exactly the assembly needed by the smooth proof; it does not restate either target. Searches recorded in the node found no existing duplicate declaration.

4. **Route and pruning — PASS.** The connected C1–C8 calculations, exceptional prime cases, and finite clopen assembly are all used. The unit route remains realized by the two original target nodes. Duplicate imports were removed; the three proper-base-change modules remain because C7 uses them. The removed direct `Sites.Gm` import is unnecessary for the compiled proof.

5. **DAG agreement — PASS.** Both target nodes now name the connected calculations, exceptional-case lemmas, and clopen assembly dependency used by Lean. The new node has complete source, proof, dependency, Lean declaration, and split metadata.

Changed during second reading: appended this review only; no proof or statement changes were needed.
