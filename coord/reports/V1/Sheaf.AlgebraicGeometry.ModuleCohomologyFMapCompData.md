## What changed

Repaired the returned delivery of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData`. Removed the duplicate
`nat_complex_injective_resolution`, `lift_nat_quasiIso`, `unique_nat_quasiIso`,
and `nat_quasiIso_globalSections_pushforward_injectives` theorem implementations.
Also removed the copied `pushforward_sections_iso` definition. Proof-only
`import all` of `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` and
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison` makes their existing
private declarations available, and the proof now calls those declarations.
The public import and the statement of `moduleCohomologyFMap_comp_data` stay
unchanged; no other module or interface is adapted.

The common-target construction, augmentation compatibility, beta homotopy,
sections naturality and composition, and three homology squares remain complete
Lean proofs. Updated the node's proof and proof_origin to record reuse rather
than duplication. Compiled the repaired module with lcompile.py without errors
or warnings. The delivery dry run checks compilation and axioms again.

## Proved and sorry left

Holes closed: 1,
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_comp_data`
(node `lem-weil-pbc-module-cohomology-fmap-comp-data`).
Holes added: 0. Split off: 0. No sorry remains in the delivered module.
The existing imported helpers are proved; this repair introduces no new theorem
or definition with a hole.

## No longer needed

No original public import was removed. Removed the earlier delivery's direct
proof imports of `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Mathlib.Algebra.Homology.Factorizations.CM5a`,
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`,
`Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`, and
`Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`:
the existing helpers now encapsulate these arguments. Their underlying results
remain dependencies of the reused proofs; this is not a claim of global pruning.

The following original planned nodes remain unnecessary for this argument:

- `lem-weil-pbc-complex-injective-resolution-mono`, module
  `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`: monicity is unused.
- `lem-weil-pbc-complex-mapping-cylinder-split-factorization`, module
  `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization`: K-injective
  comparison supplies both lifts without a cylinder.
- `lem-weil-pbc-lift-along-injective-quasi-iso`: replaced by the existing
  K-injective lifting helper and its Mathlib bijectivity argument.

No claim is made that modules shared with other proofs leave the global closure.
Rejected CompCore and CompSquares helpers and nodes remain excluded from the
delivery; their diagnostic originals are only under scratchpad.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified four statements proved twice. The earlier report
incorrectly said private helpers could not be reused: Lean's `import all` permits
access to them for this proof without changing their visibility or signatures.
This repair uses that mechanism and removes all four duplicate theorems and the
copied sections definition. No renamed or repackaged duplicate replaces them.

The earlier arbitrary-qk/qc square theorem was false; it remains excluded.
The present proof constructs actual comparison maps and establishes homotopies
before passing to homology. The unit sk-thm-p1 route is preserved: this node
realizes neither that unit's statement nor one of its numbered steps.
No new nodes, change records or forced adaptations were needed.

## Second reading by V1

1. Compared the sole delivered module with the repository using diff and a
   byte comparison of the complete existing theorem signature. PASS: the
   signature, public import, visibility, definitions and existing docstring
   are unchanged. Only proof imports, private proved helpers, local proof
   options, the proof and the author credit change. No change record or forced
   adaptation is required.
2. Compiled the delivered module with lcompile.py: PASS, no errors or warnings.
   Inspected the construction from the chosen injective replacement through
   both lift homotopies, augmentation compatibility, sections identities and
   the three homology squares. No sorry, forbidden declaration or new data
   definition occurs. A scratch copy prints axioms of the main theorem and
   all three private helpers; each uses only propext, Classical.choice and
   Quot.sound. The reused replacement and lifting theorems have complete
   proofs; no arbitrary data is chosen from an unproved existence theorem.
3. PASS: zero statements split off, zero new holes and zero new nodes. The
   three private helpers prove naturality, identification of the pinned
   sections isomorphism, and its composition law directly. Zero modules,
   zero maps, identity scheme maps and degree zero require no excluded case;
   neither monicity of lambda nor invertibility of arbitrary comparison maps
   is assumed. The rejected arbitrary-square statement is absent.
4. Searched lean/Sheaf and lean/WeilConjectures for the target and sections
   comparison identities, and repeated LeanFinder with the different query
   “canonical global sections isomorphism for composite pushforward
   naturality on cochain complexes”. Its relevant result is the already-used
   Mathlib pushforwardComp_inv_app_app, not a shorter proof of the diagram.
   PASS: existing replacement, lifting, uniqueness and sections constructions
   are reused rather than duplicated. Each proof import supplies declarations
   called in the proof. The No longer needed list covers every old dependency
   removed from proof_deps. Read dag/units/sk-thm-p1.json: this tool node is
   absent from its realized statement and numbered steps, whose route is
   unchanged. No global closure pruning is asserted.
5. Compared both node files and read the updated steps against the Lean proof.
   PASS: only proof, proof_deps and proof_origin differ, and proof_deps is
   exactly the union of the steps' uses. The steps accurately record the
   reused helpers and componentwise sections arguments.

Second reading changed no Lean code or node: the repaired proof passes. Added
this independent review and refreshed the scratch axiom check to test the
current repaired file, rather than the earlier duplicate-helper version.
