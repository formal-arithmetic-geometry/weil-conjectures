## What changed

Completed `Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural` without changing its
statement, visibility, universes, or existing definitions. The coordinates are the
additive equivalences induced by the top-open components of
`tensorPullbackObjUnitToUnit`; their bijectivity follows from
`tensorPullbackObjUnitToUnit_isIso`.

The private proved helper `tensor_unit_smul` applies the tensor adjunction Hom
bijection, its left and right naturality equations, `pushforward_map_smulHom`, and
`smulHom_naturality`. The private proved helper `unit_map_eval` evaluates the resulting
module-map equality at the top open and uses commutativity to obtain the exact
factor order in the statement. Applying the stipulated components of theta proves
the scalar-action clause, for arbitrary schemes and arbitrary global functions.

Restriction compatibility is separated into the new module
`Sheaf.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation`, imported privately.
The existing node records the actual construction and combination of these parts.
The source of the separated step is the original node's Stacks Tags 0096, 01CA,
and 03DR equation (35.8.1); its complete adjunction calculation is in the new
module's docstring and node. No arbitrary witness of mere existence was chosen:
the only adjunction chosen here is the adjunction determining the already-defined
canonical structure-module map.

Validation: the two delivered modules compile together via `lcompile.py --all`.
The final required `deliver3.py --no-push` validates the delivery and axiom probe.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_etaleTensorUnit_sections_natural`
(node `lem-sc-etale-tensor-unit-sections-natural`). Its proof is complete from the
restriction equation and the existing library declarations.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorUnitRestriction_equation`
(node `lem-sc-etale-tensor-unit-restriction-equation`). Its proof is exactly
`by sorry`. This is strictly the restriction clause for the fixed canonical maps;
it asserts neither existence of additive coordinates nor scalar-action
compatibility. The original proof constructs the coordinates, establishes their
bijectivity, and proves the independent scalar clause.

There are no holes remaining in the assigned module, no holes in private helpers,
and no holes in definitions. This is a decomposition (one upper hole closed, one
lower hole added), not a net reduction of holes. Existing imported declarations
may still depend on sorry; this delivery makes no claim of axiom-free completion
of their transitive closure.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.EtaleTensorSections` from
the assigned module, replacing it with the narrower restriction equation module.
The original dependency node `lem-sc-etale-qcoherent-presheaf-functorial` remains
needed by the restriction equation and by the sections sheaf's definitions; it is
not globally pruned. No existing DAG node or existing module becomes unnecessary
in the transitive closure. The original structure-module dependency remains.
All three original public imports remain necessary to expose the unchanged
statement and its quasi-coherence instance.

The explored proof import `Sheaf.AlgebraicGeometry.EtaleStructureSectionsEquiv`
is not in the delivered files. No claim is made that this existing module is
unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt already had a compiling one-hole reduction, but had
no report or completed dry run. Its new node copied searches about cohomology and
Ext, which did not search this restriction equation. Replaced those entries with
queries actually run and logged for this item, explicitly recording LeanSearch's
service failure as unavailable.

Local source search found the related existing theorem
`AlgebraicGeometry.etaleStructureSectionsEquiv_naturality` in
`Sheaf.AlgebraicGeometry.EtaleStructureSectionsEquiv` (node
`lem-sc-as-sequence-construction-helper-restriction`). It states the compatibility
for canonical coordinates after ULift. Mathematically, it contains the separated
restriction equation. Multiple attempts to specialize it, including explicit
ULift cancellation helpers, sheaf-compose identification, component evaluation,
and unfolding the canonical coordinates, timed out at the 60-second file limit;
one conversion produced a kernel deterministic timeout. No timeout limit or
compiler wrapper was changed. The remaining hole identifies exactly this
unlifted section equation rather than relocating the whole assigned statement.
A future worker should first revisit reuse of that existing theorem.

The unit record `sk-prop-cd` has empty realized lists. This delivery preserves the
unit's route and only expands the original node's restriction step. Empty schemes,
zero and unit scalars, identity arrows, and composites impose no extra hypotheses:
the construction uses adjunction identities and module-map equalities throughout.

## New nodes

`lem-sc-etale-tensor-unit-restriction-equation` states only the canonical normalized
restriction equation. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleTensorUnitRestrictionEquation.lean`; its node is
`dag/nodes/sec-curve-estimates/lem-sc-etale-tensor-unit-restriction-equation.json`.
It records the two existing dependencies, the source of the step, its complete
adjunction proof, genuine Mathlib searches, and the overlap with the existing
lifted naturality theorem. No statement/interface changes or forced adaptations
are included, so no change record is required.

## Second reading by D3

1. Compared the delivered `Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural` module with
   the repository version. The theorem statement, visibility, universes, and existing definitions
   are byte-for-byte unchanged; only proof code and the proof import changed. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. There are no compiler errors,
   forbidden declarations, or `sorry` occurrences outside the explicitly named split theorem
   `etaleTensorUnitRestriction_equation`. The original target theorem is fully proved. Verdict: pass.

3. Read the split theorem and its node. It is the strict normalized restriction equation for the
   canonical maps, with the same hypotheses and conclusion needed by the naturality conjunct;
   it does not restate the target or add assumptions. Its source, proof description, and node are
   recorded. Verdict: pass.

4. Checked the proof route and pruning. The coordinates are the top-open components of
   `tensorPullbackObjUnitToUnit`; bijectivity uses its existing isomorphism theorem, scalar
   compatibility uses adjunction naturality, and restriction is isolated in the new lower node.
   The unit `sk-prop-cd` and its route remain unchanged. The former direct proof import is replaced
   by the narrower restriction-equation module. Verdict: pass.

5. Checked DAG agreement. The target node proof and `proof_deps` match the Lean proof, and the
   new node has the required statement, source, proof, searches, Lean declaration, chapter, and
   unit metadata. Verdict: pass.

Changed only this report section after the first reading; no Lean statement or definition was
changed.
