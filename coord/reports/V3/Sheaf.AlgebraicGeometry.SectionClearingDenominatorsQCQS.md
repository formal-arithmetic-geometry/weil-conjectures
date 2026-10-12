## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict_qcqs`
with its statement unchanged. Adapted the proved finite affine-cover construction from
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`: affine localization provides
local lifts, compact-open scalar torsion handles overlaps, and sheaf gluing constructs the
required global section. Added proof-only imports of `SectionNonvanishingZeroLocus` and
`QuasicoherentSectionPowerTorsion`. Updated the existing node's proof route.

The key simplification is to express each twisted overlap difference in the basis of
`L.tensorPow a` from its first chart. This reduces overlap vanishing to a section of `F`
itself, allowing the already proved compact-open scalar torsion lemma to apply. Empty
covers and zero exponents are handled by finite suprema and the existing tensor-power API.
No new definitions or statements were introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict_qcqs`
(node `lem-sc-p1-section-clearing-denominators-qcqs`). No holes remain in the item;
no holes were added. This is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.Coherent` (the statement uses Mathlib quasi-coherence).
- `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent`.
- `Sheaf.AlgebraicGeometry.SectionRestrictionSTorsion`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (already supplied by the
  statement imports).

The proof no longer needs `lem-sc-invertible-tensor-qcoherent` or
`lem-sc-p1-section-restriction-s-torsion`, and does not need to prove their modules for
this item. Both are replaced by `pqf-lem-qcoh-compact-section-power-torsion` applied to
`F`, after untwisting the difference with a local basis. Existing public imports are
retained to preserve the module's public interface. No other original proof-dependency
nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original overlap route is valid but unnecessarily requires the quasi-coherence of
the twist and tensor-power torsion on an open subscheme. The existing compact-open scalar
torsion declaration already proves what is needed after untwisting. The original source
clearing-denominators theorem requires a separated morphism to an affine base and cannot
be applied directly under the target's qcqs hypotheses.

Searches: LeanFinder returned the structure-sheaf compact/qcqs torsion lemmas, not a
module version. Loogle did not recognize the project's compact-open module lemma.
The search-service grep returned no hits; direct repository rg found the proved module
lemma in `QuasicoherentSectionPowerTorsion.lean` and the proved locus identification in
`SectionNonvanishingZeroLocus.lean`. Both new dependencies are existing proved generic
tools; their use preserves the unit route (finite affine lifts, overlap torsion, gluing).

## Second reading by V3

1. **Repository comparison:** The theorem signature and all existing declarations are
   byte for byte unchanged from the repository version. The only source changes are the
   proof body and proof-only imports documented above; no target statement or definition
   was altered. Verdict: pass.

2. **Compilation and proof audit:** The delivered module compiles with
   `lcompile.py` without errors or warnings. It contains no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by`; no definition contains a proof hole. The
   delivery preflight checks declaration axioms. Verdict: pass.

3. **Statement and dependency review:** No statements were split off and no new nodes
   were introduced. The existing target remains exactly the qcqs clearing-denominators
   theorem, and the proof uses the already proved compact-open torsion and nonvanishing
   locus lemmas. The revised DAG proof dependencies match the imports and proof route;
   removed torsion and tensor-quasi-coherence dependencies are genuinely unused. Verdict:
   pass.

4. **Pruning and route:** The proof follows the unit route: finite affine trivializing
   cover, local denominator clearing, overlap torsion, common exponent, and sheaf gluing.
   It shortens only the overlap implementation by untwisting through a local basis, with
   no unit step bypassed. The report lists every removed proof-only import and no target
   closure module is incorrectly claimed pruned. Verdict: pass.

5. **DAG and documentation:** The node's `proof`, `proof_deps`, and `proof_origin`
   describe the Lean proof, and the report records the unchanged statement, closed hole,
   and mathematical rationale for the dependency change. Verdict: pass.

Changed in this second reading: appended this review section only; no Lean code, node,
or statement required repair.
