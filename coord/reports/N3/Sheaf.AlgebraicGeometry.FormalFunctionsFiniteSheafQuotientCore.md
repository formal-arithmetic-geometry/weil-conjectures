## What changed

Completed `AlgebraicGeometry.formalFunctionsFinite_sheaf_quotient_iso` with its
statement and all public signatures unchanged. Restored the proved private
`power_quotient_iso` helper, now using the public proved theorem
`Scheme.Modules.idealData_recursive_power_comparison` instead of private lemmas
from a retired module. Its inverse isomorphism identifies the two multiplication
images, and `cokernel.mapIso` identifies the quotients compatibly with projections.
The proved private `ideal_quotient_congr` transports the quotient along the
finite immersion kernel equality. Composing this with the closed-immersion unit
quotient and the tensor-pullback comparison proves the required map equation.
The existing finite-map closedness proof is unchanged. The node records this
route. No definitions or statements changed, so no consumer adaptations or
change records are required.

The complete module compiled without warnings using `lcompile.py` in 10.5 seconds.
The delivery dry run is run separately after this report is finalized.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.formalFunctionsFinite_sheaf_quotient_iso`
(node `lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso`).
Retained the already proved
`AlgebraicGeometry.formalFunctionsFiniteι_isClosedImmersion`.
Zero remaining holes; zero holes added; zero split-offs. All private helpers are
proved. This is a proof, not a decomposition.

## No longer needed

Removed `import all Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`.
Neither that module nor its upstream replacement
`WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero` is needed
by this proof. Removed the corresponding proof dependency
`lem-weil-pbc-ideal-power-product-restriction-zero`; the proof never uses the
restriction-zero theorem. Replaced it with the existing public power-comparison
module `Sheaf.AlgebraicGeometry.IdealDataRecursivePowerComparison` and node
`lem-pc-ideal-data-recursive-power-comparison`. Other proof dependencies remain
needed. This is pruning of this item's dependency; other library consumers may
still need the removed module. Public imports retain the existing interface.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt directly imported the upstream private power lemmas, but the
published build lacked that upstream object file. Importing the older compiled
Sheaf module compiled, but the current source wrapper only re-exports the
upstream module: `import all` through it cannot expose the dependency's private
lemmas after rebuilding. The public power-comparison theorem avoids both issues
and proves precisely the required comparison without duplicating its proof.

Directly rewriting the kernel equality inside the recursive formal quotient had
previously exhausted the heartbeat budget. The proved equality-transport helper
keeps that rewrite separate from the quotient construction. The unit route is
preserved; only a helper dependency below the unit level is replaced.

## Second reading by N3

1. I compared the delivered Lean module and DAG node with the repository versions.
   The target and existing declaration signatures are unchanged; the only module
   changes are the proof, a private helper, and the proof-only import. Verdict: pass.
2. I compiled the complete module with `lcompile.py` and searched the delivered
   files for forbidden constructs and unaccounted `sorry`s. Compilation succeeds
   without warnings; no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` occurs in the Lean module. Verdict: pass.
3. The proof uses the public recursive-power comparison, the quotient-base-change
   ideal equality, the closed-immersion quotient, and categorical adjunction
   transport. The private helpers are strictly intermediate reductions, and no
   new split-off statement was added. Verdict: pass.
4. The old private power-restriction import and dependency are pruned. The unit's
   finite-level quotient route remains intact, and the node proof and dependency
   records match the proof. Verdict: pass.
5. The node metadata, source attribution, and `proof_origin` agree with the
   implementation; no target statement or definition changed. Verdict: pass.

I changed only the second-reading report section and retained the worker's proof
   and DAG updates. The required delivery dry run is being run separately.
