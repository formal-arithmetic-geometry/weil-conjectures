## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleIteratedStrictTransform_no_exceptional_sections`
without changing its statement or either iterated-transform definition. All edits to Lean are
inside the assigned module. Added proved private helpers for sectionwise monomorphisms,
saturation of a coimage, restriction and tensor-pullback transport, the transported open,
and the exceptional-support set identity. Updated the item's DAG proof to match.

The proof applies principalization and the existing first-transform properties, then the
Cartier-factor kernel comparison. Equal kernel subobjects give isomorphic cokernels; the
coimage of restriction embeds in the direct image from the smaller complement. Naturality
of the restriction unit makes the quotient saturated there. The proof explicitly transports
that monomorphism through tensor pullback along the fibre-product pasting isomorphism.
The set identity uses injectivity of the first blowup away from its centre.

Validation: `lcompile.py` compiled the complete module without errors or warnings in
15.4 seconds. Static comparison confirms the two definitions and theorem signature
are unchanged; all Lean lines are at most 100 columns.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.moduleIteratedStrictTransform_no_exceptional_sections`
(node `lem-trf-iterated-transform-exceptional-support`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The existing dependency theorems
`moduleStrictTransform_properties` and `moduleStrictTransform_kernel_eq_of_cartier_factor`
are used as declared, with their existing proofs left to their assigned workers.

## No longer needed

No imports, dependency nodes or modules were removed: all six recorded proof dependencies
remain used. The proof avoids constructing a third strict transform for the product centre,
proving finite type of that product, and transporting a quotient isomorphism between
coefficient sheaves on two different schemes. The already stated kernel equality suffices
via the abelian coimage embedding. No module is withdrawn or claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof plan asked for more construction than necessary
after the kernel comparison; its steps 2–3 are replaced by a categorical argument. The unit
route is preserved, and no shared definition, statement, public import or attribute is changed.
The set proof covers both the centre and its complement, with no compactness assumption;
zero modules, empty complementary opens and unit centres require no additional hypotheses.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
