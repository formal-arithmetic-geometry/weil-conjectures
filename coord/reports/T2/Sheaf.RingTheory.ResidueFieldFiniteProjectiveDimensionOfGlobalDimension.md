## What changed

Proved `Ring.residueField_hasFiniteProjectiveDimension` without changing its signature,
visibility, or docstring. Added proof-only imports of
`Sheaf.RingTheory.ProjectiveResolutionExtCharacterization` and
`Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension`.
The bound is applied to the ULift of the residue field; the existing resolution–Ext
characterization and Mathlib linear-equivalence invariance transport it back to universe u.
Updated the item's proof plan and dependencies to record this universe transport.
Local single-file compilation is clean.

## Proved and sorry left

Closed the single hole `Ring.residueField_hasFiniteProjectiveDimension`
(node `lem-weil-pbc-residue-field-finite-projective-dimension`). No sorries remain in the
item and no new sorries were added. The proof depends on the existing sorry
`ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing`
(node `lem-weil-pbc-projective-dimension-ext-characterization`); it is not axiom-closed yet.
The new Mathlib node records an already proved declaration, not a new proof obligation.

## No longer needed

None. Both original public imports are needed by the statement. The original dependency
`def-weil-pbc-finite-global-dimension` remains needed. No original nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omits a Lean universe mismatch: the global-dimension hypothesis
quantifies over `ModuleCat.{max u v} R`, but the residue field belongs to `ModuleCat.{u} R`.
Direct application fails with an application type mismatch. The proof supplies the missing
universe transport through existing lemmas, retaining the exact original signature.
The item's recorded blueprint ancestor points to a non-blueprint intermediate node, and
`blueprint_refs.py ancestor` consequently returns None. The new node instead uses the
ancestor recorded on `lem-weil-pbc-finite-gl-dim-regular-local`, namely
`thm-weil-pbc-finite-etale-lifting`. No unit statement or realized step is bypassed.
LeanSearch was unavailable; its failure is recorded as unavailable.

## New nodes

`lem-weil-pbc-projective-dimension-linear-equiv` records the existing Mathlib theorem
`ModuleCat.hasProjectiveDimensionLE_of_linearEquiv`, read in its source with its universe
and smallness hypotheses. It introduces no module or sorry. The whole-blueprint search
for projective dimension and linear equivalence returned no matches. At n = 0 the result
is invariance of projectivity, and for zero modules the Ext groups vanish; the theorem
is already kernel-checked in Mathlib. No change record is needed because no public
interface changed.

## Second reading by T2

1. Compared the delivered Lean module with the repository version. The theorem signature,
visibility, and docstring are unchanged; only proof-only imports and the proof body differ.
Verdict: pass.
2. Compiled the module with `lcompile.py`; it is clean and contains no local `sorry`, axiom,
unsafe, opaque, or other forbidden declaration. The remaining `sorryAx` comes only from the
pre-existing imported characterization theorem. Verdict: pass.
3. Checked the proof route against Mathlib and the imported characterization. The ULift transport
uses `ModuleCat.hasProjectiveDimensionLE_of_linearEquiv` with the required universe parameters,
and the final bound is converted back by the reverse characterization. Verdict: pass.
4. Checked pruning and imports. Both public imports are required by the statement; the two added
imports are plain proof-only imports and are used by the proof. No old dependency is unused, and
the unit route and realized steps remain intact. Verdict: pass.
5. Checked the DAG updates. The item's proof and `proof_deps` record both universe-transport
steps, and the Mathlib declaration is recorded as the existing linear-equivalence result. The
new node introduces no Lean module or sorry. Verdict: pass.

Changed only the proof, its proof-only imports, the corresponding DAG proof route, and this
second-reading record.
