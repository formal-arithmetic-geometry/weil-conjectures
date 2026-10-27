## What changed

Replaced the proof hole in `ContinuousCohomology.exists_procyclicScalarCochainEvaluation`
by an assembly of the existing low-degree construction, two narrower intermediate
statements, and the existing completion-boundary descent theorem. The original public
signatures, definitions, attributes and public imports are unchanged.

The Bool-indexed low-degree theorem supplies both coordinate-specified complexes and
all coefficient maps. A private proved helper packages the coordinate-specified low-degree data.
Two further private, fully proved helpers convert actual higher cochain
primitives into local section primitives. For the finite field the cover is the identity.
For the norm-topological algebraic closure, the proof maps the cocycle into its completion,
constructs a completed primitive, applies boundary descent on `Multiplicative ℤ_[ell]`,
and transports the resulting primitives through the section coordinates. Finally the
proof applies the local sheaf criterion and constructs each normalized derived
isomorphism as `asIso` of the localization of the actual evaluation map.

Added `Sheaf.RepresentationTheory.CompleteProcyclicScalarPrimitives` for the complete
coefficient Banach/long-exact-sequence argument and
`Sheaf.RepresentationTheory.ContinuousScalarLocalQuasiIso` for the generic passage from
low section cohomology and local higher primitives to ordinary sheaf quasi-isomorphism.
Neither statement chooses data or reasserts the original existence theorem.
New proof-only imports also supply finite-dimensional completeness, completion field
instances and profiniteness of the p-adic integers; the existing public import list is
preserved verbatim. Updated
only the item's node and the two new nodes. There are no changes to another existing
module or another existing node.

## Proved and sorry left

Closed the one original hole:
`ContinuousCohomology.exists_procyclicScalarCochainEvaluation`.
No `sorry` remains in the item module, including its private field-pair instance and
its two primitive-transport helpers and the low-degree data packaging helper.

Added two holes, each exactly `:= by sorry`, with source and a complete proof in words:

- `ContinuousCohomology.complete_procyclic_scalar_primitives`, node
  `lem-sfb-complete-procyclic-scalar-primitives`.
- `ContinuousCohomology.continuousScalar_quasiIso_of_local_primitives`, node
  `lem-sfb-continuous-scalar-local-quasi-iso`.

This delivery is a decomposition: one upper hole closed and two strictly narrower holes
added, hence a net hole reduction of -1 (one additional hole overall) before downstream pruning. The existing
low-degree, Banach splitting, coinduced contraction and completion-descent holes are
unchanged, not counted as newly proved. No definition contains a hole.

The remote compiler checks all three modules in import order; final results are recorded
by the delivery tool. During debugging, profiling isolated an expensive Boolean-family
instance conversion. The private family instance uses a transparent Boolean recursor;
no shared definition was altered and no file time limit was raised. Edge cases checked in the statements and argument: empty S (the
identity cover still works for the finite coefficient field; the empty cover is permitted
in the generic criterion and boundary descent), degree two (both outside coinduced
homology degrees are positive), E=Q_l, and incomplete Omega (only its completion receives
the Banach primitive theorem). Negative degrees are handled by support hypotheses.

## No longer needed

No mathematical dependency module is globally pruned: the former complete-coefficient
inputs remain needed through `CompleteProcyclicScalarPrimitives`. The parent no longer
needs them as direct proof dependencies:
`lem-sfb-compact-function-space-complete`, `lem-coef-compact-open-currying`,
`lem-sfb-banach-translation-difference-split`,
`lem-sfb-compact-open-coinduced-contraction`, and
`lem-weil-pbc-complex-ses-homology-long-exact` now occur in that child's proof.
The obsolete direct tool approvals for currying and the long exact sequence are removed
from the parent; finite-extension completeness remains directly used. The child uses
currying and the long exact sequence as the same generic tools already approved in the
parent, not as a replacement of any unit route.

Removed direct proof imports of `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`,
`Mathlib.Topology.ContinuousMap.Compact`, `Mathlib.Topology.CompactOpen`,
`Mathlib.NumberTheory.Padics.MahlerBasis`, and
`Mathlib.Algebra.Homology.HomologySequence`. Their analytic or homological content now
belongs to the complete-coefficient child or is supplied by the finite-dimensional
completeness theorem, rather than being unfolded in the parent.

The old direct proof import of
`Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates` is replaced by
`ContinuousProcyclicLowDegreeEvaluation`. The homogeneous-coordinate construction remains
below the coinduced contraction; it is not withdrawn or duplicated.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The DAG correctly described the
analytic route, but the substantial complete-coefficient and sheaf-homology assembly
steps did not have standalone Lean interfaces matching their uses. The two new statements
isolate exactly these steps. The new local criterion explicitly receives the structural
zero-map-preservation instance needed to form its section complexes; the item constructs
this instance by reflexivity. This avoids relying on a private dependency instance being
exported by an ordinary module import.

The new nodes inherit the existing null nearest blueprint ancestor and its via chain.
The current blueprint paragraph (3), the unit record and the node's full proof were read.
Blueprint searches for procyclic, complete procyclic, local primitives, local
quasi-isomorphism and section cohomology found no duplicate of either new statement.
The existing finite-ring procyclic two-term statement and torsion cohomological dimension
statement have different coefficient and conclusion hypotheses. Searches with msearch.py
are recorded in searches.jsonl and copied accurately into the new nodes.

## New nodes

`lem-sfb-complete-procyclic-scalar-primitives` states only higher continuous primitive
existence for a complete normed Q_l coefficient field with arbitrary profinite parameter.
It extracts original steps 2 and 3, uses the existing Banach translation splitting and
coinduced contraction, and leaves the low-degree construction, incomplete coefficient
descent, internal modules, coefficient compatibility and derived normalization outside
its conclusion. Its source and three-step proof are in its node and module docstring.

`lem-sfb-continuous-scalar-local-quasi-iso` is a generic sheaf criterion with explicit
sectionwise low-degree isomorphism and local higher-primitive hypotheses. It asserts no
existence of complexes, continuous cochain formulas or analytic primitive theorem. It
extracts original step 5, using the existing internal/section-module equivalence and
exact sheafification of underlying abelian presheaves. Its three-step proof explains
separately low, higher and negative degrees. No change record is required: the existing
interfaces have not changed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
