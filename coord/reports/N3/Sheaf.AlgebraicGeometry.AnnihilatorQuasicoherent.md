## What changed

Proved `AlgebraicGeometry.annihilator_subsheaf_quasicoherent` with its original signature and
original docstring unchanged. The proof establishes both principal-open localization
conditions: lift a numerator in F, clear finitely many ideal-generator denominators, and
use the affine image hypothesis to lift to G; transfer the zero criterion using the mono.
Added proof-only imports of `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`, and
`import all Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` (for its already proved
private `Scheme.Modules.isFiniteType_over` helper). All original public imports remain.
Ideal quasi-coherence is proved locally by the closed-immersion pushforward and kernel
results, avoiding a duplicate module-level declaration and the large HilbertPolynomial import.
Updated the existing DAG node's proof, proof dependencies, and proof origin to this route.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.annihilator_subsheaf_quasicoherent`.
Added zero holes; zero split-off statements; no sorry remains in the delivered module.
This is a proof, not a decomposition. A scratch-copy `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for this theorem.

## No longer needed

The old proof dependencies no longer used are:
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`def-weil-pbc-module-localization-away`, `def-weil-affine-spectrum`, and `pqf-def-coherent`.
They are replaced by the existing affine localization and principal-open criteria.
No original module import was removed; no module is claimed to be pruned from the targets'
import closure. The remaining old dependency
`lem-weil-pbc-quasi-coherent-finite-type-affine` is used.

The first worker's duplicate private helpers `isFiniteType_over` and `ideal_quasicoherent`,
including their unused `True` parameters, were removed. Restriction finite type now reuses
an existing proof; ideal quasi-coherence is a local proof block.

## Where the brief, the DAG or earlier work was wrong

The first worker's report said the helpers were localized, but the submitted Lean file
still declared two private theorems with unused `True` parameters to evade duplicate
statement checking. Such parameters do not remove the mathematical duplication.
The second reading removed that workaround. No target statement, definition, or unit
route was changed. The DAG's original tilde-construction plan is replaced below the unit
level by the source library's proved principal-open criterion.

## Second reading by N3

1. Compared the sole delivered module against the repository using diff and checked the
   existing theorem signature byte for byte. Verdict: identical signature and docstring;
   no definitions or other existing declarations changed; only proof-only imports added.
2. Compiled the repaired module locally through lcompile.py without warnings or errors.
   Scanned for sorry and forbidden declarations; none occur. Ran #print axioms in a
   scratch copy: only propext, Classical.choice, Quot.sound. Verdict: fully proved.
3. No statement was split off and no new module-level statement remains. Searched the
   library for restriction finite type and ideal quasi-coherence, including alternate
   names and msearch grep. Reused the proved private restriction theorem via import all.
   The ideal theorem in HilbertPolynomial has the same kernel proof; the local block
   avoids importing its unrelated cohomology machinery. Checked zero/unit ideals,
   empty finite generator families (Finset.sup is zero), empty affine opens, and f=0/1.
   Verdict: no new holes, duplicate statements, hollow definitions, or arbitrary data
   chosen from an unproved existence theorem.
4. Read the principal-open criterion, both affine localization lemmas, the finite-type
   affine criterion, and the existing finite-type restriction construction. The numerator
   argument genuinely uses the finite spanning family and the mono, then applies the
   existing criterion; it is not a restatement. All added imports supply proof inputs.
   No longer needed lists every old proof dependency omitted by the new route. Read
   dag/units/sk-thm-p1.json: its realized statement and steps are unchanged; this node
   is below the unit level. Verdict: shortest practical route with the unit route kept.
5. Read the item's node and checked proof steps, proof_deps, and proof_origin against
   the Lean code. Added the finite-pushforward node explicitly for the restriction helper
   only (not its stronger main theorem), with no Noetherian or finite-morphism assumption.
   No new nodes. Verdict: records agree with the proof.

Changed during second reading: removed both dummy-True private helpers; reused the
existing finite-type restriction proof; localized the ideal kernel proof; corrected the
report and DAG dependency description. The main finite-generator proof was retained.
