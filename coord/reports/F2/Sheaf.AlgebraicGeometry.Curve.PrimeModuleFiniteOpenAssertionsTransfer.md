## What changed

Repaired the returned duplicate `AlgebraicGeometry.IsCurve.assertions_of_iso` by
**generalizing it in place** to the private `assertions_of_retraction`. It now takes
arbitrary maps a : F → G and b : G → F with a ≫ b = identity, plus explicit
implications transporting constructibility, primary torsion and invertible-order
torsion from F to G. No reverse identity or isomorphism is required. This is a
strict generalization: F may be a proper direct summand of G.

The proof uses the left inverse on cohomology to transfer vanishing and finiteness,
and naturality to transfer comparison injectivity and surjectivity. A local adapter
specializes this helper to the two isomorphisms needed by the main theorem. It does
not reproduce the old eight-field isomorphism proof. Removed the cohomology
isomorphism construction; all new data are concrete maps, not chosen witnesses.
Only the item module and its existing node change; the public signature is unchanged.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.IsCurve.prime_module_finite_open_assertions_transfer`
(node `r1-prime-module-finite-open-assertions-transfer`).
No local sorry remains and no hole is added. The private retraction helper and
torsion transport are fully proved. Pre-existing holes in imported dependencies
remain transitive obligations. Single-file compilation passed without warnings.

## No longer needed

Removed the original proof import
`Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions` and dependency
`lem-weil-pbc-curve-assertions-finite-pushforward`, replacing them with
`FinitePushforwardModuleAssertions` and `b3-finite-pushforward-module-assertions`.
The integral coefficient realization and coefficient bridge are not needed.

Removed the duplicate isomorphism-specific `assertions_of_iso` declaration and
`cohomologyEquiv` definition. Isomorphism-specific comparison transport helpers
are unnecessary: local comparison arguments now handle actual retractions.
No import of `ReducedConstantLowerShriekAssertions`, `RetractAssertions`, or
`UnderlyingAbelianAssertions` is needed. The first has only a private matching
helper; the second is restricted to integral coefficient realizations and torsion
CurveCoefficientPair data; the third requires constructibility on both sheaves,
which is not a hypothesis of this item. No global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The previous repair moved the comparison proofs locally but retained the duplicate
`assertions_of_iso` statement and was rightly refused. The existing matching
helper in `ReducedConstantLowerShriekAssertions` is private and cannot be reused
by an import. This repair takes the return's permitted generalization route,
with a genuinely more general split-monomorphism statement and a different
cohomology argument. It changes no existing library signature or visibility.

Updated the node's proof and proof_origin to describe retraction transfer.
The unit route is unchanged. The previous second-reading section was removed
because it describes the superseded delivery; this repair awaits a fresh reading.

## Second reading by F2

1. **No accidental interface changes.** I compared the delivered module with the repository version. The public theorem signature is byte-for-byte unchanged; only proof-private declarations, imports, and the node's proof metadata differ. No definition or public visibility changed.

2. **Proof validity.** The delivered module compiles cleanly with `lcompile.py`. It contains no local `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. A scratch `#print axioms` reports only the permitted logical axioms plus transitive `sorryAx` from imported open statements. The retraction proof uses concrete maps and a stated left-inverse, with no arbitrary witness data.

3. **Statements and reuse.** The existing target statement is unchanged. The private generalized retraction helper is strictly more general than an isomorphism-specific helper and is used only to transport the eight assertions. I searched the library and the recorded Mathlib searches; no reusable public declaration duplicates this argument. No new public split-off statement or node was introduced.

4. **Pruning and route.** The proof follows the unit route: assertion transport, module-valued finite pushforward, then finite-open comparison. The obsolete integral finite-pushforward import and its node dependency are removed, while the module-valued theorem and comparison dependencies remain. The imported `Pullback` module is needed for `Scheme.IsConstructibleSheaf.of_iso`.

5. **DAG agreement.** The node's proof steps and `proof_deps` match the delivered proof: module-valued finite pushforward and finite-open comparison are the only external proof dependencies. The unit and target metadata remain unchanged, and no new nodes or change records are required.

I changed only this second-reading report section; no Lean source repair was necessary after compilation and comparison.
