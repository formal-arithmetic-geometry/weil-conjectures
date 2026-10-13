## What changed

The signature of `AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre` is unchanged.
Its proof now uses `Sheaf.AlgebraicGeometry.RadicialSeparatingGenericField` to obtain a
separably generated field mapping scheme-theoretically dominantly to the reduced generic
fibre. Two fully proved private helpers complete the argument: separably-generated tensor
reducedness and `pullbackSpecIso` give geometric reducedness of the field spectrum;
quasi-compact scheme-theoretic dominance persists under flat field base change and then
passes reducedness to the fibre. The universal-homeomorphism homeomorphism transports
the specialization characterization of the generic point.

The affine radicial separating-field construction is in one new module with a named
public theorem. The original MakeSeparablyGenerated proof import moves to that module.
The tensor-reducedness import remains in the target module and is now actually applied.
The node's proof route and dependencies match these imports and the Lean argument.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre`
(node `lem-sbc-radicial-reduced-flat-generic-fibre`). No `sorry` remains in the target module.

Added one hole: `AlgebraicGeometry.exists_radicial_separating_generic_field`, node
`lem-sbc-radicial-separating-generic-field`. This constructs the affine radicial base and
an injective generic coordinate-ring map into a separably generated field; it does not
assert the target's geometric reducedness conclusion or genericity of the lifted point.
Its source and full proof in words are in the docstring and node. This is a decomposition,
with one hole closed and one added, not a proof free of `sorry` dependencies.

Both private helpers are fully proved. Both delivered modules compile without warnings
using `lcompile.py --all`.

## No longer needed

Removed the direct import `Sheaf.FieldTheory.MakeSeparablyGenerated` from the target
module. Its node `lem-weil-pbc-make-separably-generated` remains needed through the new
construction module, so it is not pruned from the transitive target closure.

No node or module is pruned from the transitive closure. The new construction module imports scheme-theoretic dominance directly instead of the unused geometric-reducedness module; existing public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error was found. The original DAG's steps leave substantial
affine scheme/field construction glue between the two field-theory dependencies and
the target. The new node records that remaining construction; Lean now completes the
geometric reducedness and generic-point transport steps from it.

## New nodes

`lem-sbc-radicial-separating-generic-field`, in
`lean/Sheaf/AlgebraicGeometry/RadicialSeparatingGenericField.lean`, states the affine
radicial construction and the compatible quasi-compact scheme-theoretically dominant
map from a separably generated field spectrum. Its proof follows Stacks Tags 0559 and
030R and uses the existing finite purely inseparable field-square theorem. Searches
found geometric reducedness tools but no matching scheme construction; LeanSearch
returned an internal server error, recorded as unavailable. Characteristic zero,
nonempty generic fibre, and empty special fibres were checked in the source argument.
No arbitrary data are chosen in a definition, and no change record is required because
all existing signatures and public imports are preserved.

## Second reading by R2

1. **Statements and accidental changes.** I compared both delivered modules with the repository versions. The existing declaration `AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre` has the identical signature and unchanged hypotheses and conclusion. The added declaration is the separately named construction node and does not restate the target: it omits the target's geometric-reducedness and generic-point conclusions while supplying only the separating-field morphism needed by the target proof. Verdict: pass.

2. **Compilation and proof status.** I compiled the two-module sandbox with `lcompile.py --all`; both modules compile cleanly. The target module has no `sorry`; the only remaining `sorry` is the whole proof of `AlgebraicGeometry.exists_radicial_separating_generic_field`, with its source, proof sketch, and matching node. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was found. Verdict: pass.

3. **New statement and searches.** The new construction statement is true in the stated generality by the affine construction in Stacks Tags 0559, 030R, and 04KM: finite purely inseparable base extension, reduced generic tensor field, and the induced affine dominant map. It is strictly weaker than the target and is used as its first reduction. The node records grep, LeanFinder, and LeanSearch results (including the unavailable LeanSearch result). No duplicate declaration was found in Mathlib or the existing Sheaf library. Verdict: pass.

4. **Route and pruning.** The target proof follows the delivered node, the existing separably-generated tensor-reduced theorem, and the universal-homeomorphism generic-point argument. The unit route remains recorded; no unit-level statement was changed. The removed direct `MakeSeparablyGenerated` import is still used by the new construction module, and the target's remaining imports are used. No additional node or module can be pruned. Verdict: pass.

5. **DAG agreement.** The target node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof. The new node's statement, Lean declaration, proof steps, source, and dependency agree with `RadicialSeparatingGenericField.lean`; its split is recorded as one decomposition (one hole closed, one strictly lower hole added). Verdict: pass.

I replaced the unused public `Mathlib.AlgebraicGeometry.Geometrically.Reduced` import in the new construction module by `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`, which supplies a notion used by its statement. No existing module interface, proof, or node statement was changed. Scratch-copy `#print axioms` checks confirm that both private helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the public construction and target additionally use the expected `sorryAx` from the named construction hole.
