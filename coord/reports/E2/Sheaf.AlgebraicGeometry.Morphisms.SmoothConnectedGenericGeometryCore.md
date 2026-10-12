## What changed

Replaced the original hole in
`AlgebraicGeometry.Scheme.smooth_connected_generic_geometry_core` by a complete
Lean proof. The existing signature and docstring are byte for byte unchanged.
Added two proof-only imports: `WeilConjectures.AlgebraicGeometry.Regular` and
`Sheaf.RingTheory.SmoothNormalRing`. The proof obtains integrality using existing
geometric irreducibility/reducedness results, proves normality of total-space
stalks on affine charts using smooth normal-ring ascent, and proves normality
of generic-fibre stalks from regularity and unique factorization.

Removed the first worker's two undelivered split modules and nodes rather than
shipping their clause restatements and circular dependencies. Updated the
existing item's proof, proof_deps and proof_origin to describe the actual proof.
No existing declaration, definition, public import or target signature changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry_core`
(node `lem-sbc-smooth-connected-generic-geometry-core`). One of one local holes
closed. Holes added: none. No `sorry` remains in the delivered module.

The proposed holes `smooth_connected_generic_generic_fibre_core` and
`smooth_connected_total_space_core` were removed with their undelivered modules
and nodes, not counted as closed baseline holes. This delivery is not a
one-hole-to-two-hole decomposition.

The axiom probe for the item prints only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The latter comes from the existing imported
`RingHom.Smooth.isNormalRing`; this is a local closure using an existing open
proof dependency, not a claim of comparator-complete proof. Separate probes of
`GeometricallyIrreducible.of_smooth_of_geometricallyConnected`,
`GeometricallyReduced.of_smooth`, `IsRegular.isIntegral` and
`IsRegular.uniqueFactorizationMonoid_stalk` show only the three standard axioms.

## No longer needed

No repository import, old proof dependency or previously reachable module was
pruned: the original proof_deps was empty and all three public Mathlib imports
are needed by the unchanged signature. The two proposed split modules and
nodes are discarded sandbox work, not repository pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker split off the generic-fibre and total-space clauses with all
of the target hypotheses unchanged, then assembled them by conjunction. Both
new nodes cited the parent theorem as a proof dependency, making that proposed
DAG circular once the parent is updated to cite them. Their docstrings also
omitted the details establishing nonemptiness and irreducibility. The report
had claimed a valid strict decomposition without recording the parent node's
actual dependencies. All these faults are eliminated by removing the split.

The shorter route is already in the library: `Regular.lean` proves geometric
irreducibility and geometric reducedness of smooth geometrically connected
families, and Mathlib descends these to integral total space without a
Noetherian hypothesis on the integral base. The existing normal-ring theorem
then supplies exactly the affine normality ascent needed.

## Second reading by E2

1. Compared every proposed module against the repository. The only existing
   module changed its proof and proof-only imports; its full existing theorem
   signature, universes, visibility and docstring are unchanged byte for byte.
   The two added modules were not repository declarations and are removed.
   Verdict: no change to any existing statement or definition.
2. Compiled the original three-file proposal, then the repaired single module
   using lcompile.py. The repaired proof compiles without errors or warnings
   and contains no sorry or prohibited declarations. A scratch copy with
   #print axioms verifies the standard axioms plus the explicitly identified
   existing imported sorryAx. No definition or arbitrary choice from an
   unproved existence theorem was added. Verdict: a complete local proof,
   conditional on the already open normality-ascent dependencies.
3. Read both proposed split statements and their nodes: they were clause
   restatements, with a circular proof dependency on the parent. Removed both.
   Searches: LeanFinder for smooth preservation of normal local rings;
   Loogle for geometrically irreducible schemes and irreducible spaces;
   Mathlib grep for reducedness descent and irreducibility over a point;
   repository rg for normal/smooth, connected/integral and generic/dense.
   These led to the existing Regular and SmoothNormalRing declarations.
   No split statement is delivered. Edge cases checked: the proof requires
   no finite dimension, perfect field, quasi-compactness, separatedness or
   Noetherian base. S is nonempty and reduced by IsIntegral; its component
   set is a singleton. Cη is connected (therefore nonempty) by the exact
   pullback instance of geometric connectedness, and only Cη needs local
   Noetherianity. Every chosen affine open contains a specified point, so
   localization and domain arguments avoid empty-chart problems.
   Verdict: no new unproved statement, no weakened hypothesis or conclusion.
4. Read the top theorem first, then the existing library and Mathlib routes.
   Retained all three public imports needed by its signature and added only
   the two proof imports directly used. The generic-fibre and normality
   geometry of the original argument is preserved; total-space integrality
   follows by the shorter proved all-fibres route. Inspected
   dag/units/sk-prop-input-spreading.json: its realized statement/step lists
   are empty, and no realized unit node or required unit step is bypassed.
   Verdict: shorter route below the unit level, no missing pruning entry.
5. Updated the existing node's proof to the actual sequence of Lean
   applications and affine localization transports; proof_deps is exactly
   the union of cited existing nodes, namely the connected-regular-integral
   theorem and smooth normal-ring ascent. Other already proved library and
   Mathlib applications are explicitly named in the steps. Its statement,
   source, stmt_deps, unit and chapter are unchanged. There are no new nodes
   requiring split-node metadata. Verdict: the delivered DAG agrees with
   the repaired Lean proof, without the proposal's circular dependencies.

Changed by second reading: replaced the clause-only decomposition with the
actual proof from existing results, removed both split modules/nodes, and
rewrote the report and existing proof metadata. No interface change record is
needed.
