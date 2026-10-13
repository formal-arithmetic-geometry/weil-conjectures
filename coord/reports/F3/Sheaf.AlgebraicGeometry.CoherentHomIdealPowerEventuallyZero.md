## What changed

Proved `AlgebraicGeometry.Scheme.coherent_hom_ideal_power_eventually_zero` in
`lean/Sheaf/AlgebraicGeometry/CoherentHomIdealPowerEventuallyZero.lean` with its original
signature, visibility, and docstring. All existing public imports stay unchanged; the added
imports are proof-only.

The proof constructs the canonical abelian image of the given map. Quasi-coherence,
finite affine sections of the coherent source, and the affine-cover finite-type criterion
make that image coherent. A direct germ argument and stalk exactness show its support is
contained in the closed complement. The existing support-power theorem supplies a killing
exponent. The affine annihilator criterion, explicit ideal-power range computations,
submodule map identities, and injectivity of the product inclusion prove vanishing for
every transition factorization. Sheaf separatedness gives the global equality.

Added proved private helpers for product quasi-coherence, affine multiplication ranges,
affine detection of zero maps, quasi-coherence and ranges of powers (including exponent
zero), affine power-product ranges, and vanishing of a stalk map from zero restriction.
These introduce no public interfaces and no holes. Updated the existing node's proof,
proof dependencies, and proof origin to describe the compiled argument and its four
additional existing dependency nodes.

Read the original source statements and proofs at
[Stacks Tag 01YB](https://stacks.math.columbia.edu/tag/01YB) and
[Stacks Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9).
The proof expands the omitted injectivity argument of 01YB using 01Y9, as planned.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.coherent_hom_ideal_power_eventually_zero`
(node `lem-weil-pbc-coherent-hom-ideal-power-eventually-zero`).

No `sorry` remains in the item; no hole was added or split off. All private helpers are
proved. The complete file compiled without warnings through `lcompile.py`.
An explicit `#print axioms` check of the theorem returned exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`; the diagnostic command was
removed from the delivery source afterward.

## No longer needed

None. No original import, dependency node, or module from the planned proof is pruned.
The proof uses all seven original proof dependencies. The four additional existing
nodes are the affine coherent-sections finiteness theorem, quasi-coherent tensor affine
comparison, stalk exactness, and affine-cover detection of zero ideal-power products.
Exploratory redundant direct imports of the source quasi-coherent-cokernel module and
Mathlib ideal operations were removed before delivery; neither was present originally.
The source sheaf quasi-coherence module remains needed for its unit instance.

## Second reading by F3

1. Compared the delivered module with the repository version. The theorem signature and
existing declaration interfaces are byte-for-byte unchanged; only proof-only imports,
private helpers, and the proof body were added. Verdict: pass.

2. Compiled the complete module with `lcompile.py` and searched for forbidden constructs.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
The theorem's axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. Checked each private helper and the theorem against the imported library declarations and
the Stacks 01YB/01Y9 argument. The affine range, stalk, support, and annihilator reductions
are true at exponent zero as well as positive exponents, and no split-off statement was added.
Verdict: pass.

4. Checked the proof route against the unit record and the node's planned steps. The route
retains the coherent image, support-power, and affine-cover detection steps; all added imports
are proof-only and the report's dependency list matches the proof. Verdict: pass.

5. Checked the node metadata and its proof/proof_deps/proof_origin against the compiled proof.
The existing node is updated only with the realized route and dependencies; no statement or
definition changed. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof repair was needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement, definition, or unit route was changed. The original module
had only statement imports, rather than the proof-dependency imports mentioned in the
standing brief; all needed declarations were added as proof-only imports.
The bundled affine ideal-product theorem exposes powers only for positive exponents;
the proved private helpers handle exponent zero explicitly, so no hypothesis restricting
`n` or the killing exponent was introduced.
