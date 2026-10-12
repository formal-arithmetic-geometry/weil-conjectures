## What changed

Proved `AlgebraicGeometry.Scheme.integral_ideal_generic_stalk` with its existing signature
unchanged. The field clause uses Mathlib's function-field instance, injectivity uses
`quasi_coherent_ideal_zero_set_affine`, and the remaining clauses use two proved smaller
intermediate theorems. Each new theorem has its own module and DAG node:
`IntegralIdealAffineSections` and `IntegralIdealGenericStalkEquivalences`.
The function-field imports are proof-only. Removed the unused import of
`Sheaf.Topology.PresheafModuleStalkFunctor`. No definitions or existing statements changed. The import visibility change and all
downstream users are recorded in `coord/changes/integral_ideal_generic_stalk_imports.md`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.integral_ideal_generic_stalk` (1 of 1).
Also closed both holes proposed by the first worker:
`AlgebraicGeometry.Scheme.integral_ideal_nonzero_iff_affine_sections`
(node `lem-weil-pbc-integral-scheme-ideal-generic-stalk-affine`) and
`AlgebraicGeometry.Scheme.integral_ideal_nonzero_iff_generic_stalk`
(node `lem-weil-pbc-integral-scheme-ideal-generic-stalk-stalk`).
No holes added or left in delivered modules; zero statements split off with `sorry`.
Scratch copies compiled with `#print axioms` for all three declarations; each uses only
`propext`, `Classical.choice`, and `Quot.sound`. All five unchanged direct importers
also compiled against the delivered modules.

## No longer needed

Removed the direct import of `Sheaf.Topology.PresheafModuleStalkFunctor` from the item.
No claim is made that it disappears from the entire targets' import closure.
The old direct proof dependencies no longer used by the item's assembly are:
`def-weil-irreducible-components`, `lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-spec-domain-stalks-function-field`, `def-weil-pbc-module-stalk`,
and `def-pc-scheme`. The affine-spectrum and fraction-field planned lemma nodes are
replaced by proved Mathlib declarations. The irreducibility, scheme and module-stalk
foundations occur in the new intermediate nodes' proof routes rather than the assembly.
The item retains `def-pc-integral-scheme` and
`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine` and uses the two new proved nodes.
The unit `sk-thm-p1` and all its `realized` statement and step nodes are unchanged;
this item is below the unit level, not one of those realized nodes.

## Where the brief, the DAG or earlier work was wrong

The first worker left two holes while closing one, so its work was a decomposition,
not a completed proof. Its docstrings did not give complete arguments, it put two new
statements in one module, and its pruning report omitted replaced dependencies.
Mathlib's closed support and generic-point calculations close the affine criterion.
A direct germ argument closes nontriviality, and the existing affine zero-set theorem
closes surjectivity. The first worker's proposed statements are true; no weakening or
statement repair was necessary.

## New nodes

`lem-weil-pbc-integral-scheme-ideal-generic-stalk-affine` records the proved criterion in
`lean/Sheaf/AlgebraicGeometry/IntegralIdealAffineSections.lean`. Its proof uses full support
on a reduced scheme and the zero prime at the generic point of an affine domain.

`lem-weil-pbc-integral-scheme-ideal-generic-stalk-stalk` records the proved stalk criterion
in `lean/Sheaf/AlgebraicGeometry/IntegralIdealGenericStalkEquivalences.lean`. Its proof uses
the affine criterion, the affine zero-set theorem, and germ representation and equality.
Both nodes have actual search records and complete natural-language proof docstrings.
The import visibility change is recorded in
`coord/changes/integral_ideal_generic_stalk_imports.md`; no existing statement or definition changed.

## Second reading by T1

1. Compared the item with the repository version using `diff`. Its existing declaration
signature is byte for byte unchanged; only imports, the noncomputable section and proof
changed. There are no other existing modules in the delivery. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`. No errors, warnings,
`sorry`, forbidden declarations, or data constructions from unproved existence theorems.
Checked all three declarations with `#print axioms` in scratch copies. Verdict: pass.
3. Read both intermediate statements and proofs, searched Mathlib with different support
and generic-point queries using leanfinder, loogle and grep, and searched both library
roots. LeanSearch was attempted and its service failure recorded without a verdict. No duplicate statement was found; existing partial results are used. Checked the
zero and unit ideals, fields and affine domains, empty affine opens (excluded by
Nonempty), and non-affine integral schemes via affine neighborhoods. An integral scheme
itself is nonempty. Both statements are strict parts of the item and now proved.
Verdict: pass.
4. Replaced both open arguments with shorter routes through Mathlib and the proved
zero-set theorem; removed unused proof imports and documented every replaced old direct
proof dependency above. Read `dag/units/sk-thm-p1.json`: its realized route is retained.
Verdict: pass.
5. Read the item node and both new nodes against the Lean proofs. Updated the new module
paths, verbatim signatures, proof steps, dependency unions, proof origins, and actual
search records; retained all required creation, source, chapter and unit fields.
Verdict: pass.

Second reading changed: proved both intermediate holes, separated their modules,
completed their proof docstrings, minimized imports, corrected DAG proof routes/searches,
and corrected the progress and pruning report. No existing signature changed.
