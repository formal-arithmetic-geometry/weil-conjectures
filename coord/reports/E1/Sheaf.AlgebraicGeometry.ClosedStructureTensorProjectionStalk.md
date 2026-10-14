## What changed

Proved `AlgebraicGeometry.closedStructure_projection_stalk_isIso` in
`Sheaf.AlgebraicGeometry.ClosedStructureTensorProjectionStalk`, keeping its complete
signature, visibility, and existing docstring unchanged. All existing imports remain.

At a point in the image, the proof constructs additive tensor coordinates from
`SheafOfModules.stalkTensorIso`, `exists_tensorPullback_stalk_iso`, and
`closedImmersion_pushforward_stalks`. Taking germs of the assumed section formula
identifies the stalk map with tensor symmetry. Tensor induction extends the equality
from pure germs to every tensor, and the coordinate equivalences give bijectivity.
Outside the image, both stalks are subsingleton, so the map is bijective.

The fully proved private helper `AlgebraicGeometry.projection_unit_stalk_iso`
identifies the unit-module stalk with the ring stalk using preservation of filtered
colimits by the forgetful functors. Its construction and proof follow the existing
private `unit_stalk_iso` in `ClosedImmersionUnitStalkKernel`, without importing that
larger kernel calculation or its ideal-multiplication dependencies. Linearity follows
from representing the scalar and vector on a common neighbourhood.

The item node's proof and proof origin are updated to describe the actual Lean
argument; its proof dependency list remains unchanged. There are no statement or
definition changes, new modules, public helpers, or forced adaptations. The two
transparency options are scoped to individual theorem declarations. The additional
namespace opening is scoped to the private helper proof term, and scalar-restricted
tensors use explicit module types. The interface-diff check reports no changes
visible to importers.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.closedStructure_projection_stalk_isIso`
(node `new-closed-structure-tensor-projection-stalk`).

Also proved the private elementary helper
`AlgebraicGeometry.projection_unit_stalk_iso` in full. No holes were added or split
off. No `sorry` remains in the delivered module. This is a proof, not a decomposition.

The final module compiles through `lcompile.py` without errors or warnings in
17.9 seconds, below the 60-second limit. A scratch copy with `#print axioms` compiled in 24.8 seconds and reported exactly
`propext`, `Classical.choice`, and `Quot.sound` for the main theorem, with no
`sorryAx`. The delivery dry run also performs the maintainer's axiom probe.
The declaration-diff check reports no changed existing statements and no new holes.
The argument handles the empty immersion through the off-image branch, the identity
immersion through tensor symmetry, and the zero module through the same equivalences;
there are no nonzero, nonempty, or finite-type hypotheses.

## No longer needed

None. No imports were removed. All three planned proof dependencies are used:

- `lem-pc-ringed-space-module-stalk-tensor` /
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor`;
- `lem-weil-pbc-module-stalk-pullback` /
  `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`;
- `lem-weil-pbc-closed-pushforward-stalks` /
  `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`.

The unit's route is preserved. No planned node or module is bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The planned proof dependencies already
provide proved comparisons with the germ formulas and scalar compatibility needed
for this calculation. The only extra elementary glue is the proved unit-module
stalk comparison. Both tensor entries can be represented directly as sections on Y
because the second entry belongs to the stalk of the pushforward module; their common
neighbourhood is obtained by intersection. Closed-embedding cofinality is already
encapsulated by the existing pushforward-stalk isomorphism.

## Second reading by E1

1. **Interface — pass.** Compared the sole delivered module with the repository
   using `diff`, and compared the complete existing theorem signature as bytes.
   The signature, visibility, docstring, and imports are unchanged. The only Lean
   additions are the proved private unit-stalk helper, declaration-scoped
   elaboration options, and the proof replacing the original hole. No definition
   or public statement changed; no change record or forced adaptation is needed.
2. **Proof — pass.** Independently compiled the delivered module with `lcompile.py`:
   no errors or warnings (22.2 seconds). Scanned for prohibited constructs and
   holes: none. Inspected the unit-stalk filtered-colimit comparison and its
   common-neighbourhood linearity argument; the scalar-restricted comparison beta;
   the section-to-germ calculation; tensor induction; and both directions of the
   final bijectivity argument. All are valid. The off-image argument uses both
   subsingleton stalks and the source zero element. All equivalences come from
   proved comparisons, not arbitrary witnesses of unproved existence statements.
   The refreshed scratch copy is the exact delivered module with a final
   `#print axioms AlgebraicGeometry.closedStructure_projection_stalk_isIso`.
   It reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Split statements — pass (none).** The original hole is closed; zero holes
   were added or split off. The private helper is fully proved and is genuinely
   smaller than the target. Checked identity immersion, empty source, zero module,
   and off-image points: no extra hypothesis is used. Searched with Loogle
   (`"stalk", "unit"`), Lean Finder (stalk functor, module tensor unit and ring
   stalk isomorphism), and `rg` across Sheaf, upstream and Mathlib. Results include
   affine Tilde comparisons and private unit-stalk calculations, but no shorter
   public comparison with the needed germ formula. The helper matches the proved
   private calculation in `ClosedImmersionUnitStalkKernel`.
4. **Route and pruning — pass.** Read all three imported comparison statements.
   Each planned dependency occurs directly in the proof; none is unused. Each
   public import supplies objects or notation in the existing signature, and
   each proof-only import is plain `import`. The unit record
   `dag/units/sk-thm-picard-duality.json` and its `realized` fields are untouched;
   no unit step is replaced or bypassed. `## No longer needed` is complete: none.
5. **DAG — pass.** The node diff changes exactly `proof` and `proof_origin`.
   Its proof describes the private unit comparison, on-image tensor symmetry,
   common-neighbourhood representatives, tensor induction, and off-image zero
   case in the delivered Lean. The unchanged `proof_deps` is exactly the union
   of the named dependencies used. No new nodes are needed for split holes.

Second-reading changes: added this review record and refreshed the scratch axiom
probe from the exact delivered source. No Lean or node repair was necessary.
