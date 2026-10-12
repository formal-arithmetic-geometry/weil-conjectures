## What changed

Proved `exists_purelyInseparable_polynomial_cover` with its exact existing signature.
Added the fully proved module `Sheaf.RingTheory.FiniteFractionRootSubstitution`, containing
`exists_finite_fraction_root_substitution` and a private polynomial coefficient-root helper.
The original module imports it and `Mathlib.FieldTheory.PurelyInseparable.Exponent` privately.
Its private `extend_from_basis_roots` constructs the embedding explicitly as a sum of rooted
basis elements, and proves the ring-map laws by injectivity of iterated Frobenius.
Updated the original node's proof route and recorded the new proved coefficient-root node.

The construction works directly with numerator and denominator polynomials over R. Their
coefficient roots are integral over R, so they lie in the integral closure immediately.
This avoids identifying rational-function fields, adjoining an auxiliary transcendental
root, and transporting through fraction-field isomorphisms. The unit and chapter route
are preserved: this is a change below the coefficient-root cover node, not a bypass of
a blueprint unit's statement or proof steps.

## Proved and sorry left

Closed the sole original hole: `exists_purelyInseparable_polynomial_cover`
(node `lem-weil-pbc-purely-inseparable-polynomial-cover`).
Also proved `exists_finite_fraction_root_substitution`
(node `lem-weil-pbc-finite-fraction-root-substitution`) and both private helpers.
There are no remaining `sorry` declarations in either delivered module; no holes added.
This is a proof, not a decomposition into unproved statements.

Both modules compile cleanly through lcompile.py. The axiom probe checks both public
results for only `propext`, `Classical.choice`, and `Quot.sound`.
The new theorem handles n=0, m=0 and zero fractions in the same construction. Prime
characteristic ensures p^n>0; R is a domain so the coefficient and fraction maps are
injective. The integral-closure coefficient map and every scalar tower are constructed
explicitly or proved, with no extra hypothesis on R. All types remain in Type u.

## No longer needed

No original imports were removed: the original four public imports support the unchanged
signature. No unproved Sheaf proof dependencies are imported.
The following original proof dependencies are unnecessary for the new route:

- `def-weil-rational-function-field`: no K(X) representation is used.
- `lem-weil-pbc-finite-of-integral-generators`: replaced by the existing Mathlib leaf
  `lem-weil-pbc-algebraic-generators-finite-extension` for a finite subfield.
- `lem-weil-pbc-finite-dimensional-domain-is-field`: E is already an IntermediateField.
- `lem-weil-pbc-integral-closure-finite-extension-normal`: coefficient roots lie in the
  integral closure directly; E need not be identified as its fraction field.
- `lem-weil-pbc-field-degree-multiplicativity`: no algebraicity/transcendence tower is needed.

These are pruned from this proof route, not asserted to be globally unreachable from all
other project targets. `def-weil-algebraic-element` is no longer a direct parent dependency
but still occurs through the finite-algebraic-generators leaf, so it is not counted as pruned.
No existing module or node was deleted or adapted.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing DAG's route is longer than necessary: writing
fractions over R makes the coefficient roots integral over R, removing the fraction-field
and transcendence identifications. Stacks Tag 032O was read online; its omitted details
are expanded by the finite-root construction and the basis-linear embedding proof.
LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder,
Loogle and source searches supplied supporting APIs, not the entire cover theorem.
The blueprint-wide coefficient-root search found no matching imported statement.

## New nodes

`lem-weil-pbc-finite-fraction-root-substitution` records the fully proved finite-family
coefficient-root construction, with a prescribed p-power exponent and the substitution
map on the entire fraction field. It is strictly a part of the argument: it mentions
no extension L, no basis of L and no embedding of L. The original theorem supplies those
and proves the assembly. The node and module contain no new hole. No change record is
needed because no existing statement, definition or visibility changed.

## Second reading by A2

1. **No accidental visible changes.** Compared the delivered cover module with the repository version. The existing theorem signature and all public declarations are byte-for-byte unchanged. The added finite-family theorem is recorded as a new node, and the report declares the added module and proof-only imports.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; both compile without warnings. Searched for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and `debug.skipKernelTC`; none occur. The public theorem bodies are complete constructions, with no hollow definitions.

3. **Split-off statement.** Checked `exists_finite_fraction_root_substitution` against its node and source. It is a strict finite-family coefficient-root sublemma, with no extension L or basis assumptions, and is needed by the cover proof. Its edge cases (empty family, zero fractions, and exponent zero) are covered by the construction and the positive prime-power exponent argument. No duplicate declaration was found in the imported library.

4. **Shortest route and pruning.** The proof uses the explicit basis-linear Frobenius construction and the finite-fraction root-substitution theorem. The old fraction-field/transcendence dependencies are not used and are listed under `No longer needed`; the unit route and its realized cover step remain intact. Imports are separated correctly: statement imports are public, and the Frobenius exponent and finite-root modules are proof-only imports.

5. **DAG agreement.** Compared both node files with the Lean declarations. The cover node's proof, dependencies, and origin describe the actual basis/Frobenius route; the new node has the required statement, source, proof, searches, Lean record, chapter, and unit fields. No statement or definition change record is needed.

I changed only this second-reading report section; no Lean proof, public signature, node, or import required repair.
