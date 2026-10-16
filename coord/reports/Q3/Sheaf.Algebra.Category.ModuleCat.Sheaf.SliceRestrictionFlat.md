## What changed

Added the proof-only module `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits`
and used its finite-limit theorem in `SheafOfModules.isFlat_over`. The upper theorem now
constructs the exactness predicate from finite-limit preservation and finite-colimit
preservation supplied by the existing closed monoidal tensor API. The item's DAG proof
and dependencies record this reduction, and the new finite-limit node records the exact
remaining extension-by-zero comparison step.

## Proved and sorry left

The original declaration `SheafOfModules.isFlat_over` is proved. The delivered module has
one sorry left, in `SheafOfModules.isFlat_over_preservesFiniteLimits`, the finite-limit
component isolated in the new node
`lem-weil-pbc-slice-restriction-flat-finite-limits`.

## No longer needed

No planned mathematical dependency was removed. The proof adds the proof-only import of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`; the extension exactness and tensor
comparison modules are also proof-only imports in the finite-limit module. The public
`Mathlib.Algebra.Category.Grp.FilteredColimits` import supplies the sheafification instances
needed by that module's signature.

## Where the brief, the DAG or earlier work was wrong

The direct plan cannot currently be completed from the available interfaces in one
statement: `ringedSlice_extension_tensor` exposes the projection formula as an
isomorphism of underlying presheaf functors, while `IsFlat` is a sheaf-level exactness
predicate. Transporting finite-limit cones across sheafification, the underlying
functors, and the extension exactness equivalence is a genuine intermediate argument.
The new node states exactly that finite-limit component and leaves the upper theorem's
colimit component fully proved by tensor-closedness.

## New nodes

`lem-weil-pbc-slice-restriction-flat-finite-limits` is stated in
`lean/Sheaf/Algebra/Category/ModuleCat/Sheaf/SliceRestrictionFlatLimits.lean` and is the
only remaining sorry. Its source is Stacks Tag 0E8J; its proof plan uses the existing
ringed-slice exactness and tensor comparison declarations together with flatness. The
change record is `coord/changes/slice-restriction-flat-limits.md`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The delivered upper proof is compiled and preserves
the original signature; the sole open node is the finite-limit component stated separately.

## Earlier second reading (a previous round; superseded)

1. **Signature preservation.** Compared the delivered `SliceRestrictionFlat.lean` with the
   repository version. The existing theorem `SheafOfModules.isFlat_over` has the same
   signature byte for byte; only its proof and proof-only imports changed. The finite-limit
   theorem is a separately declared split node, and the added module is absent from the
   repository version.
2. **Proof and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile
   cleanly. The upper theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   or `extern`. The one remaining `sorry` is the named theorem
   `SheafOfModules.isFlat_over_preservesFiniteLimits`, and its docstring and DAG node give
   the source and complete proof plan.
3. **Statements and new node.** The split finite-limit statement is exactly the finite-limit
   component needed by the upper theorem, with no weakened conclusion or added hypothesis
   beyond the explicit monoidal-structure transport argument. Its edge cases include empty
   finite diagrams through `PreservesFiniteLimits`; no existing Mathlib or Sheaf declaration
   states this arbitrary ringed-site slice result.
4. **Pruning and imports.** The split theorem's extension exactness and tensor modules are
private proof imports; `Mathlib.Algebra.Category.Grp.FilteredColimits` is public to supply
the sheafification instances needed by the signature. The upper module's tensor-closed and
finite-limit modules are private proof imports. No old proof dependency is removed from the
recorded route.
5. **Unit route.** The DAG still realizes the `sk-thm-properbasechange` route through
   extension exactness and the extension tensor comparison. The remaining split node is
   strictly below the unit and records the unresolved cone-transport step.

Changed the finite-limit module imports from public to private, preserving the public API
while making the dependency pruning explicit. No statements or definitions were changed.

## Second reading by Q3

1. **Signatures.** Compared `SliceRestrictionFlat.lean` with the repository version. The
   existing declaration `SheafOfModules.isFlat_over` has the identical elaborated
   signature; its proof-only imports and proof body are the only changes. The finite-limit
   declaration is new and is recorded by the matching split node.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`.
   `isFlat_over` has no remaining `sorry`; the only open proof is the explicitly named
   `isFlat_over_preservesFiniteLimits`, with its source, proof plan, and matching DAG node.
   No forbidden declaration forms occur.
3. **Statements.** The new theorem is the finite-limit half required by the upper proof,
   with the monoidal structure pinned by `hm`; it does not add mathematical hypotheses
   beyond that explicit instance equality. Searches recorded in its node found no existing
   theorem for arbitrary ringed-site slices. Empty finite diagrams are included by
   `PreservesFiniteLimits`.
4. **Pruning.** The extension exactness and tensor-comparison modules are private imports
   of the split module, while the public imports provide the types and sheafification
   instances occurring in its signature. No old proof dependency used by the delivered
   route was removed.
5. **Unit route.** The DAG still follows `sk-thm-properbasechange` through the
   ringed-slice extension exactness and tensor-comparison steps; the split theorem is
   strictly below that unit route and isolates the unresolved cone-transport argument.

I changed only this report section after the first delivery check; no Lean declarations,
statements, definitions, or DAG records were changed during second reading.
