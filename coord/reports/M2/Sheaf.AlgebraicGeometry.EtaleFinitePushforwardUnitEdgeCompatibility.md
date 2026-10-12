## What changed

Proved `AlgebraicGeometry.Etale.cohomology_baseChange_unit_edge_compatibility` in
`Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`, preserving its
signature and original docstring. Added two fully proved private helpers:
`counit_pushforward_unit` and `exchange_edge_apply`.

The proof follows the original adjunct argument. The source library's
`upperStarComp_inv_app_counit_app` proves the composite-counit calculation, and
`squareUpperStarIso_paste_vert_hom` supplies the sheaf-comparison coherence.
Naturality and composition of cohomology then combine the two sides. Added the
proof-only import `WeilConjectures.SixFunctors.BaseChange.Pasting` and updated the
item node's proof, proof_deps and proof_origin to match. The public import is unchanged.

Local compilation passes without warnings. The new import passes import_direction.py.
The item belongs to sk-thm-p1 but is not one of that unit's realized statement or steps;
its curve calculations and strictly henselian comparison route are preserved.
The source square-pasting node is already Lean-closed and is used as a tool.
No finiteness, invertibility of exchange, or extra pullback hypotheses are introduced.
The calculation also applies to identity squares and the empty scheme.

## Proved and sorry left

Proved the module's only previous sorry:
`AlgebraicGeometry.Etale.cohomology_baseChange_unit_edge_compatibility`
(node `lem-weil-pbc-finite-pushforward-unit-edge-compatibility`).
Both private helpers are proved. There are no sorries left in this module and no new
sorry declarations or modules. The proof uses the existing composition clause of
`AlgebraicGeometry.Etale.cohomologyPullbackFunctorial`; its dependencies remain
separate existing project items.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`;
- `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange`;
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (redundant);
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` (redundant).

Removed these direct proof dependencies from this item's node:
`lem-weil-pbc-derived-inverse-image-composition`,
`lem-weil-pbc-edge-map-base-change`, `def-weil-pbc-kinjective-resolutions`,
and `def-pc-fibre-product`. Their respective derived-composition, edge-map and
resolution modules are unnecessary for this proof. Fibre products are not constructed
in the proof; the given square witnesses suffice. The edge-map and fibre-product nodes
remain in the unchanged informal statement dependencies; this report claims only that
this proof no longer needs them, not that other targets do not use them.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's derived-composition theorem and explicit
K-injective choices are unnecessary: the source library already proves sheaf-level
square pasting and cohomology naturality. The original declaration docstring is kept
as its API; the updated node and inline comments describe the actual shorter route.
The suggested generic rewrites on cohomology required explicit congruence/combination
proofs because functor-object expressions do not always match by rewrite transparency.

## Second reading by M2

1. **No accidental visible changes.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof code, private helpers, proof-only imports, and the corresponding DAG proof metadata differ. No change record is required.

2. **Proof checks.** Compiled the module with `lcompile.py`; it succeeds without warnings. Searched the delivered files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `debug.skipKernelTC`; none occur. The target's transitive `#print axioms` includes only the permitted foundational axioms plus `sorryAx` from existing open dependencies.

3. **Split statements.** No statements were split off and no new nodes or sorries were added. The two private helper lemmas are fully proved and are not public restatements of the target.

4. **Pruning and route.** Checked the proof against the DAG route and unit record. The unit's realized route is preserved. The proof uses the source counit identity, square pasting, and cohomology naturality/composition; the removed imports and direct dependencies are genuinely unused and are listed above under `## No longer needed`.

5. **DAG agreement.** The node's proof, proof dependencies, and proof origin describe the implemented route. The public import remains unchanged; the added `BaseChange.Pasting` import is proof-only. No statement or definition was altered.

**Changes made during second reading:** none; the delivered proof and metadata passed all checks as submitted.
