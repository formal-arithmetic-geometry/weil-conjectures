## What changed

Proved `AlgebraicGeometry.exists_integral_field_hypersurface_presentation` in
`Sheaf.AlgebraicGeometry.FieldHypersurfaceIntegralPresentation`, without changing its
signature, visibility or original docstring. Added four proved private helpers for
Frobenius independence and separating bases, geometric reducedness of the fraction
field, primitive-element hypersurface coordinates, and the quotient fraction-field
algebra equivalence. Updated the node proof to match this route.

All added imports are proof-only: `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.FieldTheory.SeparablyGenerated`,
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `Mathlib.RingTheory.Flat.Basic`,
`WeilConjectures.Mathlib.RingTheory.LocalProperties.Reduced`, and
`WeilConjectures.RingTheory.GenericIrreducibility`.

The primitive-element construction adapts the proved source-library perfect-field
argument after its separating-basis input. The kernel argument uses the existing
proved `GenericIrreducibility.dvd_of_aeval_eq_zero`. The characteristic-p argument
adapts the existing Frobenius-independence proof, with the algebraic closure in the
same universe. The final base-section equality is proved by naturality of
`Scheme.ΓSpecIso`, rather than a new compatibility assumption.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_integral_field_hypersurface_presentation`
(node `lem-sbc-field-hypersurface-integral-presentation`).

No holes added; no `sorry` remains in the delivered module. All four private helpers
have complete proofs. This is a proof, not a decomposition. The construction handles
an empty transcendence basis, algebraic extensions, the trivial extension, arbitrary
characteristic, and non-perfect base fields. It assumes no geometric irreducibility.
Single-file compilation passed; the delivery dry run performs the axiom probe.

## No longer needed

None: the original module had no proof-dependency imports or proof-dependency nodes.
All original public imports are retained because its statement uses them. No modules
or nodes are claimed pruned. No new splitting modules are delivered.

## Where the brief, the DAG or earlier work was wrong

The node's plan had no named proof dependencies. The source library already contains
a proved hypersurface-coordinate construction and its Gauss-lemma kernel argument,
although its coordinate-existence theorem assumes a perfect field. Replacing only
that theorem's initial input by a finite separating basis allows reuse of its full
remaining argument for this theorem's arbitrary base field. The implemented relation
is chosen with minimal total degree, rather than explicitly clearing denominators
of a minimal polynomial. The original statement is unchanged and true.

The unit `sk-prop-normal-form` has empty realized arrays for its statement and steps;
this below-unit proof changes neither the unit statement nor its route.

## Second reading by K1

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, private helpers, and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. Searched for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none remain. The proof uses only ordinary Lean and imported theorems. Verdict: pass.
3. Checked the split-off material: there are no new public statements or new nodes beyond the existing item node, and no `sorry` was added. The private helpers are strictly intermediate reductions and are fully proved. Verdict: pass.
4. Checked the route from the target downward. The proof uses the geometric-reduced tensor argument, finite separating basis, primitive-element hypersurface construction, and fraction-field equivalence; it preserves the unit route and removes no imports or dependencies. Verdict: pass.
5. Checked DAG agreement. The item node's proof origin and proof steps describe the implemented route, and the node's Lean declaration and statement match the module. Verdict: pass.

I changed only the report by adding this second-reading record; no Lean statements or definitions were changed.
