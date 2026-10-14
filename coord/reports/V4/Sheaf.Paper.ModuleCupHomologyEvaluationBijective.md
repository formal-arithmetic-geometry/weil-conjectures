## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cupHomologyEvaluation_bijective` in
`Sheaf.Paper.ModuleCupHomologyEvaluationBijective`, with the existing signature,
visibility, generator definition and public import unchanged. Adapted the already
proved degree-zero private argument in `Sheaf.Algebra.Homology.DerivedFreeModuleHomology`
to arbitrary integer degree using two fully proved private helpers. Projective-source
vanishing and the truncation triangle prove that homology is bijective on maps from
k[-n]; the canonical single-complex homology isomorphism and evaluation at 1 then
identify the composite with the precise `cupHomologyEvaluation` map by `rfl`.

Added proof-only imports `Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
Updated the existing node's proof, proof_deps and proof_origin, and the theorem's
proof docstring, to describe the implemented route. No other module is adapted.
Single-file compilation succeeds without warnings. The proof is uniform in n and A,
including unbounded A and the zero ring, and introduces no extra assumptions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.cupHomologyEvaluation_bijective`
(node `lem-sc-module-cup-homology-evaluation-bijective`).
The private helpers `projective_single_to_lower_eq_zero` and
`projective_single_homology_bijective` are also fully proved.
No sorry remains in the delivered module; no sorry is added anywhere.
This is a proof, not a decomposition. Recompiled the saved proof during this session.
An explicit `#print axioms` probe for the theorem and both private helpers reports
only `propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.
The delivery dry run passes, with the independent second reading still to follow.

## No longer needed

Removed the proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`.
The implemented route does not use node `lem-pc-ring-derived-map-representative`
(`CochainComplex.IsKProjective.Qh_map_bijective`) and removes it from proof_deps.
It needs no chain-map/homotopy-class calculation, no K-projectivity instance for
the single complex, and no essential-surjectivity transfer for the target A.
These are pruning statements for this item's proof; other consumers may still
need the K-projective node and module. The evaluation definition and derived
homology definition dependencies remain. No blueprint unit statement or realized
step is bypassed: `sk-prop-av-cube.realized` has empty statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The original argument is mathematically valid, but its step 2 hides a substantial
chain-map/homotopy quotient calculation. The library already has a fully proved
truncation argument in degree zero; extending it to n avoids that calculation
and proves this theorem outright. No false or unusable statement was found.
No signatures, definitions, targets, or other workers' modules were changed.

## Second reading by V4

1. Interface preservation: PASS. Diffed the sole delivered module against the
repository. The existing theorem signature and ambient variables are byte for
byte identical; visibility and the public import are unchanged. The canonical
`cupHomologyEvaluation` definition remains in its unchanged upstream module.
No definition, target, or other module is changed; no change record is required.

2. Proof and trust: PASS. Independently compiled the delivered file without
errors or warnings. Compiled a fresh scratch copy with `#print axioms` for
`cupHomologyEvaluation_bijective` and both private helpers: each uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered
module contains no sorry, axiom, unsafe, opaque, extern, implemented_by, or kernel
checking bypass. The selected representative comes from a proved theorem and
is used only within a proof; no object is defined by arbitrary unproved existence.

3. Split statements and small cases: PASS. No statements were split off and no
holes were added. Read both fully proved private helpers, checking the strict
bound n-1, the shifted bound n-2, both exactness arguments, and cancellation in
the homology square. The source is the single object concentrated in degree n;
the proof covers negative n, n=0, zero P, the zero ring, and unbounded targets.
The final `rfl` checks the precise canonical generator, rather than a selected
representability equivalence.

4. Shortest route and pruning: PASS. Searched lean/Sheaf and lean/WeilConjectures
by homology bijectivity and projective-single vanishing, read the existing
private degree-zero argument, and independently searched Mathlib's derived
category sources and Lean Finder with the query "Morphisms out of a projective
object placed in degree n are determined bijectively by their induced map on
nth cohomology". The results concern Hom-complex cohomology and projective
resolutions, not a shorter exact theorem for this evaluation map. The existing
private degree-zero helper is not a public all-degree result. Each new proof
import supplies used infrastructure (free-module projectivity, projective-source
vanishing, and truncation/shifted-heart comparison); all remain plain imports.
The old dependency `lem-pc-ring-derived-map-representative` is the only removed
proof dependency, and its KProjective import is listed above. Checked the unit
record and its statement/step: no realized node is bypassed, and no unit record
is modified. No claim of whole-library unreachability is made.

5. DAG agreement: PASS. Only `proof`, `proof_deps`, and `proof_origin` differ
from the repository node. Its statement, statement dependencies, Lean signature,
source, chapter, and unit are unchanged. The dependency list is exactly the union
of the steps' uses; the steps describe the compiled vanishing, truncation, and
canonical-evaluation argument. No new node or open theorem is introduced.

Second-reading changes: corrected the shift notation from P[n] to P[-n] in the
proof docstring, helper comment, and node's proof steps: a single complex in
degree n is the shift P[-n]. No Lean proof body or signature needed repair.
The blueprint section file named by the unit is absent on this machine; the
complete statement and step are available and were read in the unit JSON.
