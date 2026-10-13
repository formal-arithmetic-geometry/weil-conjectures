## What changed

Replaced the rejected same-statement core wrapper with a strict decomposition.
`Sheaf.AlgebraicGeometry.AffineChartOrdinaryHomComparison` now imports
`Sheaf.AlgebraicGeometry.AffineChartCanonicalHomNaturality` only for its proof.
Every existing declaration and definition keeps its signature, visibility and body
except the original theorem's proof.

Constructed canonical scalar-extension composition isomorphisms using the cocone
ring-map equation and Mathlib's `ModuleCat.extendScalarsComp`. Proved their unit-tensor
formulas. The parent proof uses `ModuleCat.ExtendScalars.hom_ext` to identify both supplied
normalized isomorphisms with the canonical ones, then cancels the target isomorphism
from the algebraic square. It substitutes the resulting formula for phi into canonical
geometric naturality. Both modules compiled in import order (10.2 and 25.0 seconds).

The remaining geometric theorem applies only to the canonical image of a stage map.
It has no arbitrary limit map phi, no eP or eQ, no normalization hypotheses and no square
hypothesis. The removed algebraic step is proved here, rather than moved into that hole.
The constructions remain concrete; no definition selects data from an unproved theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.affine_chart_ordinary_hom_comparison`
(node `lem-pc-affine-chart-ordinary-hom-comparison`) by a complete Lean proof from the
strictly smaller canonical geometric comparison and Mathlib.

Added one hole: `AlgebraicGeometry.affine_chart_canonical_hom_naturality`
(node `lem-pc-affine-chart-canonical-hom-naturality`). Its entire proof is `by sorry`.
This is a decomposition: one original hole closed, one lower hole added, net zero;
the affine geometric comparison itself is not yet proved without sorry.

Proved without sorry: `AlgebraicGeometry.scalarExtensionCompOfEq_one_tmul` and
`AlgebraicGeometry.colimitScalarExtensionComp_one_tmul`. The corresponding isomorphism
definitions `scalarExtensionCompOfEq` and `colimitScalarExtensionComp` contain no holes.
No sorry remains in the item's module; this is the only sorry in the delivery.

Edge cases: the normalization proof works for zero modules and zero rings because
unit tensors still generate the scalar extension. The geometric comparison uses affine
quasi-coherent equivalence, not a nonempty-chart assumption, so empty affine charts
are included. Mutually comparable indices are handled through antisymmetrization and
the starting representative's isomorphism. Finite presentation is never assumed.

## No longer needed

No imports removed and no original dependency module pruned from the import closure.
All original public imports are needed by the unchanged definitions or statements.
The parent proof's direct dependencies are replaced by canonical naturality; the
original upper-tail limit data, fibre products, quasi-coherence and ordinary recovery
predicate remain needed in the lower geometric obligation. The old direct `proof_deps` are now delegated to the lower geometric node:
`new-affine-chart-upper-tail-limit-data`, `def-pc-fibre-product`,
`pqf-def-coherent`, and `def-pc-chart-ordinary-map-recovery`. Each remains a
proof dependency of that node, and the relevant definitions still occur in the
parent's unchanged statement. No original DAG node is claimed globally unnecessary. The previous `affine_chart_ordinary_hom_comparison_core`
wrapper is discarded; it was an unpublished same-statement copy, not a useful reduction.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt only renamed the same hole. That has been removed. The DAG's
geometric steps use definitions and an upper-tail limit theorem, but no existing
listed declaration supplies affine Hom naturality for these explicit charts. The
new node isolates that geometric step. The tensor-generator uniqueness and square
cancellation portions of step 3 are now proved in Lean. The unit's realized lists
are empty; no unit statement or prescribed unit step is bypassed.

The LeanSearch service returned Internal Server Error; the recorded search marks it
unavailable, without treating that as evidence of absence. LeanFinder, Loogle and
Mathlib/project/DAG text searches were also performed.

## New nodes

`lem-pc-affine-chart-canonical-hom-naturality`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-chart-canonical-hom-naturality.json`, states
the canonical geometric naturality portion of the parent comparison. Its module is
`Sheaf.AlgebraicGeometry.AffineChartCanonicalHomNaturality`. The parent node's proof,
proof dependencies and proof origin now follow the written Lean proof. No interface
change or forced adaptation is made, so no change record is required.

## Second reading by P4

1. Compared both delivered module paths against the repository. The canonical
   module is new. In the existing module the diff is exactly one plain proof
   import and replacement of the original `by sorry` body. Every existing
   signature, visibility, docstring and definition body is byte-for-byte
   unchanged. No target, hypothesis, conclusion or data construction changed.
   Verdict: pass; no change record or adaptation required.

2. Independently compiled both modules with `lcompile.py --all`: canonical
   module 9.4 s, parent 20.7 s, exit 0. Scanned both sources: exactly one
   `sorry`, the complete public named theorem
   `affine_chart_canonical_hom_naturality`; no forbidden declarations or hollow
   definitions. A scratch copy with `#print axioms` for all eleven declarations
   compiled in 24.4 s. The four new algebraic constructions/lemmas and five
   existing definitions use only the three permitted axioms (or fewer).
   The parent and the canonical geometric theorem additionally use `sorryAx`,
   as the report explicitly discloses. Verdict: valid decomposition, net zero
   holes; the geometric assertion remains open, not an axiom-free proof.

3. Read the split theorem's full statement, docstring and node. Its P,Q are
   actual pullback sections; its comparisons are asserted in a proposition,
   never selected as data by a definition. It handles only canonical images
   of s; the parent separately proves uniqueness of arbitrary normalized
   eP,eQ and solves the square for phi. Thus it is a proper geometric part of
   the argument, not the rejected same-statement core wrapper. Unit tensors
   generate even for zero modules/rings; affine equivalence and pullback
   pasting cover empty affine charts. The starting representative is merely
   equivalent to j, which gives an isomorphism, and the argument does not
   assume antisymmetry of I or finite presentation. No empty-index assumption
   is missing: the supplied j makes the tail nonempty. Verdict: true as stated
   and exactly the remaining geometric obligation. New searches used
   LeanFinder (tensor product natural isomorphism), Loogle (homEquiv/pullback),
   and grep (pullback iso/equiv/tensor and fullyFaithful/extendScalars).
   Read upstream `Modules/PullbackTilde.lean` (tildePullbackIso,
   pullbackSpecΓEquiv and their generator formulas), Mathlib tilde full
   faithfulness, and project affine Hom/sections comparisons. These are
   supporting APIs; none supplies the explicit limit-ring and chart-pasting
   naturality. Finite-presentation section-model results and derived Hom
   comparison results have different hypotheses/categories. Closing the
   remaining theorem requires these geometric identifications and is not a
   few-minute application of an existing declaration.

4. Read the proof from its conclusion upward: normalization is exactly
   ModuleCat.ExtendScalars.hom_ext plus the existing Mathlib composition
   generator formula; cancellation is elementary category algebra. The new
   import is plain `import`, since it only supports a proof. Each original
   public import and each new module's public import supplies symbols or
   colimit instances needed by the unchanged signatures/constructions.
   No module is pruned. Checked all four old direct proof dependencies: they
   are moved to the lower node, not removed from the closure. Read
   `dag/units/sk-thm-picard-semicon.json`: its statement and sole step have
   empty realized lists, and no realized unit route is bypassed. Verdict:
   pass, after making the direct dependency accounting explicit in the report.

5. Checked the parent node's three steps against the actual obtain,
   tensor-generator extensionality and cancellation proof. Its proof_deps is
   exactly the new canonical naturality node. The new node has source,
   statement dependencies, proof steps with their union as proof_deps,
   proof_origin, search records, status, created, blueprint ancestry,
   chapter/unit and Lean record; its verbatim statement matches Lean.
   Its proof dependencies retain the original geometric obligations.
   Verdict: pass. Corrected the first worker's combined prose grep query to
   the actual logged regex, and appended the independent search records.

Second reading changed only report/dependency accounting and new-node search
metadata. No Lean repair was needed; both algebraic generator lemmas were
already fully proved. One original hole is closed and one strictly smaller
geometric hole is added: decomposition, not net proof progress.
