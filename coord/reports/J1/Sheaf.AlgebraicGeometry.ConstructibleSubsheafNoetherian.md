## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_mono_noetherian`
in `Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian` without changing its
signature. Use the existing proved finite-value/source-predicate comparison on both
sides and the existing proved Noetherian-coefficient subobject theorem. Mathlib infers
Noetherianity of the finite coefficient ring. Added proof-only imports
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and
`Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian`. Updated the original
node's proof, proof_deps and proof_origin to this route and updated the theorem docstring.
The unit `sk-prop-sf-cbc` has no realized statement or steps; the new route still uses
generic constancy and Noetherian induction through the existing subobject theorem.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_mono_noetherian`
(node `lem-weil-pbc-constructible-subobjects-noetherian`). No sorry remains in the
item, and no new theorem or sorry is introduced. The existing imported declarations
are proved in their source files; any remaining sorries in their dependency closure
remain existing project work. The item compiled without errors or warnings using
`lcompile.py`. The original hypotheses cover the empty scheme and zero ring/sheaf;
the reused theorem and comparison impose no extra nonemptiness or nonzero hypotheses.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

Removed all six original direct proof dependencies of this node:
- `lem-weil-pbc-constant-subsheaf-generic`
- `lem-weil-pbc-irreducible-lisse-strata`
- `lem-weil-pbc-flat-lfp-open`
- `lem-weil-pbc-noetherian-finite-components`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`

These are no longer direct obligations of this proof. Some underlying geometry and
stalk infrastructure is still used transitively by the reused generic-constancy and
Noetherian-induction results; no claim is made that all six nodes are globally
unreachable. The public imports remain to preserve the module's existing public API.

## Where the brief, the DAG or earlier work was wrong

The original plan duplicates the now-existing Noetherian-coefficient subobject
argument. The comparison theorem bridges the two predicates exactly, so it is
unnecessary to formalize the generic calculation again. No statement error found.
Both new proof imports passed `tools/import_direction.py may` (no cycle).
Searches: `msearch.py` leanfinder for constructible subsheaf closure, loogle for
`IsNoetherianRing`, and grep for `constructible_of_mono_noetherian`, plus local `rg`
over both library roots. The local library search found the reusable declarations.

## Second reading by J1

1. **Unchanged statement.** Compared the delivered module with the repository version. The theorem
   signature is byte-for-byte unchanged: the same Noetherian scheme, finite commutative coefficient
   ring, sheaves, monomorphism, and constructibility hypothesis and conclusion are present.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors or
   warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`, and no definition contains a placeholder proof. The proof uses the existing
   comparison theorem and Noetherian subobject theorem; the finite-ring Noetherian instance is
   inferred without adding a hypothesis.
3. **Statements and dependencies.** No new theorem or split-off statement was added. The two
   imported declarations are existing library results, and local searches found no duplicate
   declaration. The node's proof, proof dependencies, and proof origin agree with the Lean proof;
   the removed imports and old direct dependencies are listed above.
4. **Shortest route and pruning.** The comparison theorem followed by
   `constructible_of_mono_noetherian` is a shorter valid route than reproving generic constancy and
   Noetherian induction here. The public imports remain unchanged; only proof-only imports were
   replaced. The removed imports and dependencies are recorded in `## No longer needed`.
5. **Unit route.** The unit `sk-prop-sf-cbc` has no realized statement or proof steps, so there is
   no unit-level route to bypass. This node remains below the unit and uses the established generic
   constructibility and Noetherian-subobject results. No statement error was found.

Changed in this second reading: added this review section only; no Lean or DAG changes were needed.
