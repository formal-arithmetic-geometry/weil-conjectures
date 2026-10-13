## What changed

Proved `Algebra.flat_tensor_fibre_polynomial_append_of_regular_sequence` with its signature
and visibility unchanged. Added the proved module
`Sheaf.RingTheory.PolynomialAppendClosedFibreParameters` and its node. This helper establishes
regular locality, dimension and the appended-variable generators of the source closed fibre
from `MvPolynomial.exists_polynomial_local_closedFiber_equiv` and
`MvPolynomial.polynomial_origin_regularLocal`.

The main proof computes the extended ideal `K = p₀L`, constructs the local quotient map,
checks the parameter images against `hseq`, applies the existing proved
`RingHom.flat_of_regular_parameters`, and transports flatness through Mathlib's
`quotIdealMapEquivQuotTensor`. The new proof imports are ordinary, non-public imports.
Updated the original node's proof route to match these steps.

Both modules compile without warnings with `lcompile.py --all`. `#print axioms` for both
proved theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`; neither
depends on an unproved declaration. No definitions or existing
statements changed. The proof handles `t = 0`, `e = 0`, and the case of the zero prime without
extra hypotheses: variable arguments are empty when `e = 0`, the source is a residue field,
and the quotient remains nonzero because its defining ideal lies in the maximal ideal.

## Proved and sorry left

Closed the sole original hole:
`Algebra.flat_tensor_fibre_polynomial_append_of_regular_sequence`
(node `lem-weil-pbc-flat-polynomial-append-tensor-fibre`).

Also proved the new theorem `Algebra.polynomial_append_closed_fibre_parameters`
(node `lem-weil-pbc-polynomial-append-closed-fibre-parameters`).

There are no `sorry`s left in either delivered module, and no holes were added or split off.
This is a proof from existing library results, not a decomposition into new unproved statements.

## No longer needed

Removed the main module's direct proof import of
`Sheaf.RingTheory.PolynomialOriginRegularLocal`; the new source-fibre helper imports and uses it.
Its node and module are still needed transitively, so this is not a module pruned from the
closure. The old direct proof dependencies `lem-weil-pbc-polynomial-ring-origin-regular-local`
and `def-weil-pbc-mv-polynomial-ring` no longer occur in the main node’s direct
`proof_deps`; both remain dependencies of the new helper. No dependency module or node
is pruned from the transitive closure. The existing localization-Noetherian node
is implemented by Mathlib's localization instance, with an explicit proof import of
`Mathlib.RingTheory.Localization.Submodule`.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan did not name the already-proved
`MvPolynomial.exists_polynomial_local_closedFiber_equiv`, which supplies the central source
fibre identification. Reindexing the variables, transporting the extended maximal ideal,
and identifying the residue-coefficient prime with the origin completes that step in Lean.
No unit realization is bypassed: this item is below the unit's realized statements and steps.

The cited Stacks source files are absent from this machine's literature directory. Read the
primary online texts at Tags [07FH](https://stacks.math.columbia.edu/tag/07FH),
[00OP](https://stacks.math.columbia.edu/tag/00OP), and
[07DY](https://stacks.math.columbia.edu/tag/07DY). The new helper follows the existing natural
polynomial fibre theorem (00SV/0H9M) and the origin theorem (00OP); its explicit reindexing
and transport argument is recorded as agent-written.

## New nodes

`lem-weil-pbc-polynomial-append-closed-fibre-parameters` records the **proved** helper in
`Sheaf.RingTheory.PolynomialAppendClosedFibreParameters`. Its statement assumes just a field,
two polynomial primes with the specified contraction, and membership of the appended
variables in the larger prime. It concludes regular locality, dimension `e`, and generation
of the maximal ideal by their classes. It combines the existing natural polynomial closed
fibre equivalence with polynomial-origin regular locality. The node records LeanSearch's
actual unavailable result, LeanFinder's nonmatching candidates, and the local searches that
found these two existing results. There are no change records, because no existing interface
was changed.


## Second reading by W2

1. **Unchanged interface — pass.** Compared the whole main module with the repository
   using `diff -u`: only ordinary proof imports and the original `sorry` body differ.
   Its theorem signature, docstring, visibility, public imports and definitions are
   unchanged. The helper is new; no existing declaration or target changes.
2. **Kernel proof — pass.** Independently compiled both modules in import order using
   `lcompile.py --all`, without errors or warnings. Scanned both sources for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by` and `extern`: none occurs. Compiled a
   scratch copy with explicit `#print axioms` for both theorems: each uses exactly
   `propext`, `Classical.choice`, `Quot.sound`. All local data constructions are explicit;
   the extracted prime and equivalence come from an already-proved theorem.
3. **New statements — pass.** There are no split-off holes. Read the new proved helper
   downward through reindexing, transport of the extended ideal, the natural polynomial
   closed-fibre equivalence, maximality of the origin, and parameter transport. It is
   strictly the source-ring part of the main argument and contains no target flatness
   conclusion. For `e = 0` its variable list is empty, its origin is zero, and its model
   is the residue field of dimension zero. For `t = 0` the coefficient ring is `k`, with
   coefficient prime zero. For a zero larger prime and positive `e`, the variable
   membership hypothesis is impossible; a zero target prime similarly cannot support
   a nonempty regular sequence of zero elements in the nonzero fibre. Independently
   searched LeanFinder for “maximal ideal of polynomial localization quotient by
   coefficient prime generated by variables”, and grep for quotient/fibre regular
   locality, as well as `rg` in both library roots and Mathlib. No duplicate bundled
   parameter theorem was found; the existing natural fibre equivalence and origin
   theorem are correctly reused.
4. **Route and pruning — pass, report clarified.** The main proof uses the source
   parameters, proves the equality of the extended target ideal with `p₀L`, verifies
   locality and the images of the parameters, applies `flat_of_regular_parameters`,
   then transports through the quotient-tensor equivalence with its actual algebra
   structure. The imports are needed either by the signature or these steps; all added
   proof imports are ordinary. `RegularSequence` is a public helper import because
   its signature uses `Ideal.ofList`. Checked `dag/units/sk-thm-p1.json` `realized`:
   neither edited node realizes a unit statement or step, and no such step is bypassed.
   Clarified the two former direct dependencies retained through the helper; no module
   is pruned from the closure.
5. **DAG — pass after metadata repair.** The only changed fields of the existing node
   are `proof`, `proof_deps`, `proof_origin`. Both proof dependency sets equal the union
   of the steps’ `uses`, and their arguments agree with the Lean proof. The new node
   has its source, searches, creation/blueprint metadata, chapter/unit and Lean record.
   Its Lean statement had been whitespace-flattened; replaced it with the exact
   multiline declaration signature required by the brief.

Second reading changed only the new node’s verbatim Lean statement record and the
pruning explanation in this report. No Lean proof repair was necessary. One original
hole closed, zero holes added, zero split off.
