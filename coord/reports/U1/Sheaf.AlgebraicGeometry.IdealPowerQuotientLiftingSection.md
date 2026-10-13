## What changed

Closed the sole hole in `Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection` by
implementing the finite-affine globalization of Stacks 01PQ. The original signature
and public imports are unchanged. The proof adds only private proof imports.

Two new modules separate genuinely different remaining tasks:
`IdealPowerQuotientAffineLiftingSection` constructs a lift on one affine open, without
ambient compactness, quasi-separatedness, transition maps, or global descent;
`IdealPowerLocalMapsEventuallyAgree` proves eventual equality of two existing local
maps on a quasi-compact overlap, without constructing a section lift or a quotient.

The target proof chooses finite common degrees, proves composition of power
inclusions by monic cancellation, proves that these maps preserve the specified
unit sections, transports all local lifts, invokes quasi-coherent cokernel closure,
obtains a degree for each overlap, and proves that the transported maps agree at
the maximum degree. It then uses the existing morphism-gluing theorem and proves
the final evaluation equation by local equality of sections. No quotient-transition
composition lemma is needed: each second transport uses q(n,m) directly.

Compilation is through lcompile.py only. A theorem-local maxHeartbeats budget is
needed for elaborating the restricted module components; the file still compiles
within the project's 60-second limit. No existing module is adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting_section`
(node `lem-weil-pbc-ideal-power-quotient-local-lifting-section`). No sorry remains
in the assigned module.

Added, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.ideal_power_quotient_affine_lifting_section`
  (`lem-weil-pbc-ideal-power-quotient-affine-lifting-section`).
- `AlgebraicGeometry.Scheme.ideal_power_local_maps_eventually_agree`
  (`lem-weil-pbc-ideal-power-local-maps-eventually-agree`).

This is a decomposition: one upper hole closed, two strictly local holes added,
not a sorry-free proof or a positive net-hole reduction. Each new theorem has a
complete natural-language proof, source, and DAG node. The actual finite-cover
construction, degree transports, descent, and final evaluation are proved in Lean.

## No longer needed

No original import was removed; all three original public imports support the
unchanged signature. Every added proof import in the assigned module is used. The second reader removed
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` from both new helper modules;
neither statement nor its local argument requires quasi-separatedness.

Removed immediate proof dependencies:

- `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`, module
  `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`: a finite affine cover
  comes directly from Mathlib's
  `isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens`, and overlap
  compactness from `QuasiSeparatedSpace.inter_isCompact`.
- `lem-weil-pbc-ideal-power-evaluation-eventually-zero`, module
  `Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero`: its interface takes
  global maps; the overlap calculation needs maps defined only on two opens, so
  the new local agreement lemma states exactly the needed injectivity step.

These are pruned from this theorem's proof edges, not asserted to be unreachable
from all project targets. The other four removed immediate proof dependencies are
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`def-weil-pbc-module-localization-away`. Their modules are
`Mathlib.AlgebraicGeometry.Modules.Tilde` (the first two),
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, and
`Mathlib.Algebra.Module.LocalizedModule.Basic`. They are now dependencies of the
affine helper rather than immediate dependencies of the target; they are not
claimed as globally pruned.
Quasi-coherent cokernel closure and morphism gluing remain immediate dependencies.
Power monicity/injectivity from FormalPolynomialPowerLifts is also used directly.

## Where the brief, the DAG or earlier work was wrong

The plan's existing eventual-zero theorem cannot be applied directly to local
maps on an overlap: its arguments must be global sheaf morphisms. The new local
agreement theorem removes that interface gap while preserving the stated route.
The original plan also left affine annihilator/localization and the denominator
construction unstated; those are now isolated as the single-affine lifting task.

Read Stacks 01PM and 01PQ on their official pages: the local denominator argument
and the finite-affine gluing route agree with the source. There is no mathematical
statement correction. The item is below the unit's realized statements and steps;
no chapter or unit route is changed. The new lemmas were checked for the zero and
unit ideals, empty affine opens, empty overlaps, n=0, and empty schemes. For a zero
ideal use positive degree; for a unit ideal use degree zero; the finite-cover proof
uses suprema with their zero default and also works on an empty covering.

LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder,
Loogle and Mathlib grep found localization and quasi-separatedness tools but no
matching section-lifting or local-map eventual-agreement theorem. The search log
contains the actual queries. Whole-blueprint searches for ideal-power sections,
01PM, and annihilators found no duplicate blueprint statement.

## New nodes

`lem-weil-pbc-ideal-power-quotient-affine-lifting-section`, module
`Sheaf.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection`, isolates steps 1
and 2 of the assigned node. It includes the annihilator identification, relation
check in the denominator construction, and evaluation identity on every smaller
open. It has no finite-cover globalization.

`lem-weil-pbc-ideal-power-local-maps-eventually-agree`, module
`Sheaf.AlgebraicGeometry.IdealPowerLocalMapsEventuallyAgree`, isolates the overlap
injectivity part of step 3. It keeps the target module fixed and restricts only the
source ideal power to a later degree, which is sufficient before composing with q.
It constructs no lifting map. Its proof uses finite affine vanishing and sheaf
separation on the quasi-compact overlap.

No change record is required: no existing signature, definition or public import
changed.

## Second reading by U1

1. Compared the assigned module with the repository version. The target theorem signature is byte-for-byte unchanged; the two added helper signatures are new split nodes and are recorded verbatim in their DAG `lean.statement` fields. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`; the target has no `sorry`, while the two named helper declarations contain exactly their documented `by sorry` proofs. A probe reports only the allowed standard axioms plus `sorryAx` from those open helper nodes. Verdict: pass.

3. Read both helper statements against Stacks 01PM and 01PQ and tested edge cases described in the report (zero/unit ideals, empty opens and overlaps, degree zero). They are strictly smaller than the target: one is affine lifting, the other is eventual local agreement. Searches found no duplicate library declarations. Verdict: pass.

4. Checked the proof route and imports. The finite affine cover, transport, overlap agreement, gluing, and evaluation steps are present in the target proof; the unit route is unchanged. Removed unused `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` imports from both helper modules and documented all six proof dependencies pruned from the target's immediate DAG edges. Verdict: pass.

5. Checked DAG agreement: each node's `proof_deps` is the union of its proof-step uses, and both new node statements match their Lean declarations verbatim. Verdict: pass.

Changed: repaired the two helper import lists, synchronized new-node statement metadata, added second-reader search records, expanded the pruning report, and appended this review.
