## What changed

Replaced the sole `sorry` of
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedCoefficientKernels` by a complete
combination proof. The statement, its hypotheses, and its public import are unchanged.
Added two proved private helpers in the item: `image_span_generator` identifies the
image-generated ideal of a principal section ideal using `Ideal.map_span`;
`residue_kernel_comparison` derives finite type, the extended-kernel equality, and
`IsQuotientIso` from principal section kernels and a normalized common residue square.
The second helper constructs the quotient lifts on the covering image sieve and
uses naturality and the inverse residue isomorphism explicitly.

The proof privately imports the existing ConstantCompletionEquivalence module with
`import all` to reuse its proved `ideal_finiteType_of_span` and
`extension_eq_of_span` helpers. It privately imports the two new specialization
modules described below. No definition, instance, existing signature, or consumer
was changed. The generic ideal argument is proved here; only the embedded coefficient
specializations remain as lower obligations.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedCoefficientKernels`
(node `lem-sfb-embedded-integral-coefficient-kernels`). The item contains zero
remaining `sorry`s. Both new private helpers are fully proved.

Holes added, exactly two:

- `AlgebraicGeometry.ProEtale.integralModelsEmbeddedScalarFlat`
  (`lem-sfb-embedded-integral-scalar-flat`, module
  `Sheaf.Paper.IntegralModelsEmbeddedScalarFlat`). This states only flatness of
  the displayed restricted regular module; it makes none of the ideal assertions.
- `AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueSections`
  (`lem-sfb-embedded-integral-residue-sections`, module
  `Sheaf.Paper.IntegralModelsEmbeddedResidueSections`). This supplies the residue
  isomorphism, its actual commuting square, local surjectivity, and the two principal
  section-kernel formulas. It asserts neither flatness nor any of the three ideal
  conclusions; the item derives those by its private generic argument.

Thus this is a decomposition: one upper hole closed and two strictly smaller
obligations added, not a net hole reduction or a claim that the coefficient theory
is axiom-free. No existing dependency hole was changed. Each new theorem has the
exact body `by sorry`, a source, and a complete natural-language proof.

The section presentation was checked on empty objects and empty covering sieves:
the quotient proof uses local, not sectionwise, surjectivity. A principal constant
kernel has its global generator; after inverse image the multiplication-by-pi
kernel presentation remains exact. For continuous coefficients the projection
normalization fixes both the scalar map and residue maps; the kernel is generated
by the same scalar image. No new nonempty or invertibility hypothesis is used.

## No longer needed

No original import was removed and no existing module is withdrawn. The direct
proof no longer cites `lem-integral-coefficient-ext-comparison`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`, or
`det-prop-integral-criterion-constant-coefficients`; their work is isolated in the
new embedded specialization nodes, which still cite them. Consequently these
nodes and their modules are **not** globally pruned. No unit route is bypassed.
The existing `def-weil-pbc-ringed-site-ideal` dependency is retained and the direct
proof now records `lem-weil-pbc-constant-completion-equivalence` for its kernel and
proved ideal-generator/local-saturation API. The new modules' only public import
is the existing `IntegralModelsEmbedded` interface; the item's proof-only imports
add no public API.

## Where the brief, the DAG or earlier work was wrong

The supplied dependency declarations are useful but do not directly state the
needed embedded-map normalization. `integralCoefficientExtComparison` supplies an
existential equivalence preserving constructibility, without a scalar or residue
map equation. `sfb_integral_coefficient_limit` supplies the spectral positive
quotient tower and its projections. `integral_constant_completion` supplies the
spectral completion flatness and local quotient formulas. The reconstructed
embedded small-site scalar/residue maps are a further compatibility step; applying
those results by their names alone does not close it.

There is a shorter generic ideal argument than repeating the completion proof:
reuse the already proved finite-generator and ideal-extension helpers. The residue
square and local surjectivity suffice for the quotient condition. This delivery
formalizes that argument and leaves the two genuinely smaller specialization
steps. No false statement or process/tool workaround is involved.

## New nodes

`lem-sfb-embedded-integral-scalar-flat` isolates scalar flatness, the first clause
of the original second proof step. Its source is integral models paragraph (1)
and Stacks sites-modules `lemma-completion-flat` (093M). Its plan identifies the
actual completion map using normalized projections and transports flatness to the
small site.

`lem-sfb-embedded-integral-residue-sections` isolates the canonical first-residue
square and principal section formulas from the same paragraph and Stacks lemma.
Its proof in words specifies the global pi section, the finite discrete residue
isomorphism, exact constant inverse image, and the completed projection kernel.
Both nodes have Lean attachments, three search kinds, and the original chapter
and unit. No change record is needed because existing definitions and statements
are unchanged.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
