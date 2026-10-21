## What changed

Restored the assigned quarantined module from its rework archive and proved
`SheafOfModules.isIso_derivedTensor_truncationWindow` with its original signature and
public imports. Added proved private lemmas for tensoring the good-truncation triangle in either
variable and for translating the acyclic-tensor definition of K-flatness to the
source categorical predicate. Identified the existing named tensor naturally with
the source derived tensor by the resolving-subcategory localization equivalence.
Naturality transfers invertibility of the specified canonical map.

The proof uses the existing generic `DerivedCategory.isLE_tensor` and derived tensor
exactness. Explicit local monoidal instances avoid repeated expansion of the same
categorical structures during elaboration. The universal-property tensor and counit
are locally irreducible so the comparison uses their APIs instead of unfolding
choices. The DAG proof and dependencies now follow this implementation. There are
no statement, definition, visibility or consumer changes.
The added section commands and local attributes are documented in
`coord/changes/E2-derived-tensor-truncation-proof-scope.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.isIso_derivedTensor_truncationWindow`
(node `lem-weil-pbc-derived-tensor-truncation-window`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The private `tensor_truncGE_left`, `tensor_truncGE_right`, and
`kFlat_of_right_acyclic` are fully proved.
Validation: `lcompile.py` accepted the complete proof in 48.0 seconds in its final
profiling run. The temporary profiler setting is removed from this packet;
`deliver3.py` recompiles the final source and runs the delivery preflight.
Profiling identified costly counit conversions. The proof now uses the explicit
counit and its source invertibility theorem, and quotient representative APIs
avoid large equality-transport motives. The time limit is unchanged.
The proof uses existing dependency declarations, including the existing tensor-descent
interface; it does not claim their transitive axioms have all been eliminated.

## No longer needed

Removed private imports:

- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`;
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`;
- `Sheaf.Paper.ProjectionMateExact`;
- `Mathlib.Algebra.Homology.BifunctorShift` (already available through public imports);
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `Sheaf.Paper.SfCommonStageWeilCohomology`.

The direct proof dependencies `lem-pc-kflat-bounded-flat-replacement`,
`lem-pc-bounded-above-flat-kflat-site`, and
`lem-weil-pbc-ringed-projection-mate-exact` are no longer required by this proof.
The generic source tensor upper bound packages the bounded-flat calculation;
the source tensor exactness supplies the required distinguished triangles.
Standard derived homology needs no Weil cohomology construction. The already public
`WeilTensorProduct` supplies the precise tensor-descent interface used here.
Removed the two obsolete `tool_uses` approvals for the superseded bounded-flat
replacement route. No module is withdrawn: other consumers may still need all these dependencies.

## Where the brief, the DAG or earlier work was wrong

The archive contains one theorem hole, and it compiles against the current published
build. The assignment is handled by restoration plus a proof, not by withdrawal or
an empty module. The DAG's proposed bounded-flat calculation is already available
in the generic source library, so it need not be repeated. Its projection-mate
exactness dependency is much larger than necessary.

The source upper-bound node records `DerivedCategory.isLE_tensor` with an ordinary
module specialization, but the attached source declaration is generic; this proof
uses that declaration for the monoidal Grothendieck abelian category of module
sheaves. The existing source exactness theorem likewise handles arbitrary derived
objects through K-flat representatives. No unit route is bypassed.

Edge cases: the proof uses weak cutoff inequalities, so equality of either cutoff
with i minus the opposite bound is included. Lower truncation preserves the original
upper bound even when the retained interval is empty; the window conclusions then
assert vanishing in every degree. Zero objects, the zero ring and sites without
points require no additional assumptions.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
