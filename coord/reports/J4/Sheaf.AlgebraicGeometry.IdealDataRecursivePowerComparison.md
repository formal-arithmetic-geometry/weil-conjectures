## What changed

Proved `AlgebraicGeometry.Scheme.Modules.idealData_recursive_power_comparison`
with its signature, docstring and public imports unchanged. Added proof-only
imports of qcqs pushforward, affine tensor sections, affine cokernel/image,
quasi-coherent kernel and cokernel closure, unit quasi-coherence, subobjects,
linear isomorphisms and ideal operations.

The private ideal-data quasi-coherence helper uses the kernel construction and
qcqs pushforward. Proved private product quasi-coherence and multiplication-range
helpers from the affine tensor and image theorems, then proved quasi-coherence
and affine ranges of positive recursive powers by induction. The zero power's
inclusion is the identity. Affine-local detection of zero morphisms and the
cokernel/kernel universal properties give factorizations of the two mono
inclusions. Equality of subobjects gives the required compatible isomorphism.
The item's node copy records this cycle-free route and its five dependencies.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.idealData_recursive_power_comparison`
(node `lem-pc-ideal-data-recursive-power-comparison`).
No sorries remain in the item and none were added. No new modules or nodes.
The final local compilation completed in 34.8 seconds without errors or warnings.

## No longer needed

The planned proof dependency
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, module
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, is not
needed by this proof and is not imported. Its needed multiplication-range and
power-induction arguments are proved locally using the smaller tensor and
image interfaces; its quotient and restriction clauses are not used.
The original file lacked this import, so no existing import was removed.
All original public imports are retained to preserve the public interface.
Pruning here concerns this item's proof edge; the module may have other users.

## Where the brief, the DAG or earlier work was wrong

Importing the sole planned proof dependency closes a cycle through
CoherentFormalModule, ModuleSupportProperOverBase, closed-immersion pushforward,
affine pushforward base change, finite-free complexes, integral filtrations,
coherent local-free ideal lattices, and QuasicoherentOpenSectionIdealExtension
back to this item. The dry run detected and refused that first route.
The replacement uses qcqs pushforward rather than the similarly cyclic
closed-immersion pushforward module. The smaller dependencies passed import
checks and local compilation.

No mathematical statement or definition changed. The proof handles n = 0,
the zero and unit ideals, and the empty scheme: affine range and separatedness
arguments require no nonempty affine cover index or nonzero ideal assumption.

## Second reading by J4

1. Compared the delivered Lean module with the repository version. The existing theorem signature, docstring, and public imports are byte-for-byte unchanged; only proof-only imports, private proof helpers, and the theorem proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it completed without errors or warnings. Searched delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and `debug.skip`; none occur. The target's printed axioms are limited to the permitted axioms plus `sorryAx` inherited from still-open imported declarations. Verdict: pass.
3. Checked the five private helpers and the target proof against the existing declarations and searched the repository for duplicate statements. No new public statement or split-off theorem was added, and the target is not restated under another name. Edge cases n = 0, zero/unit ideals, and empty schemes are handled by the displayed cases and affine-range argument. Verdict: pass.
4. The proof follows the shortest available acyclic route found by the worker: qcqs pushforward and kernel quasi-coherence, affine tensor/image range calculations, induction on recursive powers, and subobject equality. The planned affine-sections dependency is unused and remains out of the imports; the report and node record this pruning. The unit route is preserved through the target node. Verdict: pass.
5. Compared the sandbox node with the Lean proof. Its proof steps, dependencies, and origin describe the actual qcqs/tensor/image/induction/subobject route; no new nodes or split-off holes exist. Verdict: pass.

I changed only this report by adding the second-reading record. No Lean or DAG repairs were necessary.
