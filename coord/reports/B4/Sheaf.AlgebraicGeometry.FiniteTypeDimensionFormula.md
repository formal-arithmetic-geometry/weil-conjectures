## What changed

Replaced the first worker's application of the new, unproved
`AlgebraicGeometry.affine_dimension_reduction` with a complete proof of
`AlgebraicGeometry.topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg`.
The proof chooses an affine neighbourhood, proves its coordinate algebra is finite type,
applies the existing `topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`, and proves all
local-dimension, stalk-dimension, and residue-transcendence-degree transports.
The residue-field isomorphism explicitly respects the canonical map from the base field.

Removed the first worker's helper and its undelivered node
`lem-kun-dimension-formula-affine-reduction`. Restored the original theorem documentation.
No existing statement, definition, visibility, or import changed. Updated only `proof` and
`proof_origin` of `lem-kun-dimension-formula`; its original `proof_deps` remain appropriate.

## Proved and sorry left

Closed the repository's one hole:
`AlgebraicGeometry.topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg`.
There are zero holes left in the delivered module and zero holes added elsewhere.
The first worker's added hole `AlgebraicGeometry.affine_dimension_reduction` is removed,
rather than counted as another proved declaration. No statements are split off.

Both the target declaration and the existing affine algebra theorem have been checked with
`#print axioms`: exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
This is a proof, not a decomposition. Against the repository module the direct hole count
changes from one to zero; global closure figures remain the ledger's responsibility.

## No longer needed

No repository imports, modules, or original proof dependencies are pruned. Every old
`proof_deps` entry still supplies a notion or step of the actual proof. The existing
proof-only import `Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg` remains plain `import`.
The discarded `lem-kun-dimension-formula-affine-reduction` was newly proposed in this sandbox
and has never been part of the repository dependency list.

## Where the brief, the DAG or earlier work was wrong

The first worker's assertion that `affine_dimension_reduction` was a strict substatement was
incorrect. Its witnesses include the whole dimension formula together with finiteness;
therefore it is stronger than the original conclusion and moves all substantive work into
one new hole. The target's arithmetic rewrite was sound but did not establish progress.
That helper and node are removed. The existing affine algebra theorem already gives the
needed finite witnesses, and Mathlib supplies the localization and residue-field tools;
all remaining transports can be proved in this session. No target or source correction
is needed.

## Second reading by B4

1. **Interfaces: pass after repair.** Compared the delivered module with the repository
   module by `diff` and asserted byte-for-byte equality of everything preceding the original
   theorem's `:=`. Its entire signature, original docstrings, module header, public imports,
   and proof import are unchanged. There are no other delivered modules, definitions,
   interface changes, forced adaptations, or change records. Removed the new helper and
   restored the documentation that the first worker had shortened.

2. **Proof and axioms: pass.** Compiled the replacement file through `lcompile.py`, then
   compiled an identical scratch copy with `#print axioms` for the scheme theorem and its
   affine algebra input. Both show only `propext`, `Classical.choice`, `Quot.sound`.
   The final module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`, and has no compiler warnings. All constructed maps and equivalences come from
   proved Mathlib constructions, not witnesses selected from unproved existence theorems.

3. **Split statements: repaired, then pass.** Opened the proposed helper and its node:
   the three witness equalities contained the full target formula, so the split was refused
   and removed. There are no new statements left to audit. Independently searched with
   `msearch.py`: LeanFinder query "affine open scheme dimension at a point stalk localization
   residue field algebra equivalence" found `IsAffineOpen.isLocalization_stalk` and related
   affine chart APIs; Loogle query `IsLocalization.algEquiv` found the exact localization
   equivalence construction; grep query `trdeg.*residueField|residueField.*trdeg` returned no
   hits. Also searched `lean/Sheaf`, the upstream `WeilConjectures` sources, and
   `coord/changes` by the item name, dimension-at-point, residue, and transcendence-degree
   keywords. Read `AffineResidueScalarTransport` and the upstream residue-map calculation in
   `Curve/AdelicLocal`: their relevant compatibility calculations confirm the explicit
   naturality proof here; neither supplies this dimension formula as a public theorem.

4. **Route and pruning: pass.** Read [Stacks 02FX](https://stacks.math.columbia.edu/tag/02FX)
   and its actual affine input [00P1](https://stacks.math.columbia.edu/tag/00P1).
   A locally finite type morphism to Spec K suffices; the unchanged statement also retains
   its quasi-compactness assumption. At step 1 the affine-pairs criterion applies to the
   affine top open of Spec K and the chosen affine U, without separatedness assumptions.
   Step 2 uses the affine homeomorphism and the existing open-subspace local-dimension
   theorem; the two inequalities for the homeomorphism are proved directly from the infima.
   Step 3 applies the already proved affine formula, with exactly its field, finite type,
   and prime-ideal hypotheses. Step 4 uses `isLocalization_stalk`, `IsLocalization.algEquiv`,
   `ResidueField.mapEquiv`, and an explicit `AlgEquiv.ofRingEquiv`: the naturality equality
   `hcanonical` checks the base-field action, not merely a ring isomorphism. Finally
   `ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`, and finite-cardinal coercions give the
   conclusion. Tested the interpretation on Spec K (both summands zero), generic and closed
   points of the affine line, and reducible/nonreduced affine schemes: no integrality,
   reducedness, closed-point, algebraic-closure, or characteristic hypothesis is added.
   The empty scheme supplies no x, so requires no exceptional construction.
   The unit `sk-prop-sf-kunneth-ordinary` has empty `realized.statement` and `realized.steps`;
   its route is unchanged. No original dependency or import is unused by the chosen route.

5. **DAG agreement: pass after repair.** Restored the repository node as the basis of the
   metadata and updated only its four proof-step texts and `proof_origin` to describe the
   actual Lean proof. Checked the proof dependency set equals the union of the steps' uses
   and that the original dependency list is unchanged. Statement, statement dependencies,
   Lean record, chapter, unit, source, and all other node fields are unchanged. No new nodes
   remain. Every cited original node's relevant Lean declaration or Mathlib match was read:
   affine pairs, affine chart points, open-subspace local dimension, the finite type algebra
   formula, and affine stalk localization.

The second reading changed the proof from a restatement-based decomposition to a complete
proof, removed the new hole and node, restored the original documentation, and corrected the
DAG proof description. The required dry run and delivery follow these checks.
