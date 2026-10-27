## What changed

The statement and public imports of
`Sheaf.Paper.FiniteQuotientCohomologyFiltrationTriangle` are unchanged. Its proof now
constructs the required triangle from the actual coefficient-layer triangle and
transports bounds and local models along its endpoint isomorphisms.

The new `FiniteQuotientCoefficientLayerData` module constructs the coefficient
module quotient map sectionwise, its actual sheaf kernel, the derived tensor of
the successor with that kernel, and restriction of the canonical representative
of the previous reduction. No existence theorem supplies arbitrary data.

The new `FiniteCoefficientLocalHomologyModels` module defines the ordinary
realization and local algebraic-complex comparison predicate. Its theorem
`finiteCoefficient_local_homology_models` is proved: cycles inject into a finite
term, homology is their quotient, and a finite module is finitely generated.
Vanishing outside the algebraic support descends by pushing an etale covering
sieve to the pro-etale site, pulling it back over each slice object, and applying
sheaf separatedness. These are actual Lean arguments, not additional holes.

Three further modules isolate the coefficient triangle and the two independent
outer local-complex calculations. The layer calculation uses only the residue
model; the previous calculation uses only the previous model. Neither assumes
any cohomological control of the successor. All new proof imports of the item
are private. No existing module other than the assigned item is changed.

Validation: `lcompile.py --all` compiled all six delivered modules cleanly in
import order. Their times were 7.4, 7.3, 6.7, 6.2, 5.8 and 8.0 seconds, with no
warnings. A declaration-parser comparison also confirmed the original theorem
signature and docstring are preserved.

## Proved and sorry left

Original holes closed: one, in
`AlgebraicGeometry.Scheme.finiteQuotient_cohomology_filtration_triangle`.
This is a decomposition, not a completed proof without additional obligations.

Additional theorem proved without a new hole:
`AlgebraicGeometry.Scheme.finiteCoefficient_local_homology_models`, including its
private finite-homology and etale-cover zero-detection helpers.

Three holes added, each a public theorem in its own new module with a source,
proof in words and DAG node:

- `AlgebraicGeometry.Scheme.finiteQuotient_coefficient_layer_triangle`:
  `lem-weil-pbc-finite-quotient-coefficient-layer-triangle`.
- `AlgebraicGeometry.Scheme.finiteQuotient_layer_local_complexes`:
  `lem-weil-pbc-finite-quotient-layer-local-complexes`.
- `AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes`:
  `lem-weil-pbc-finite-quotient-previous-local-complexes`.

The item has zero remaining literal holes; the delivery adds three. Relative to
this item's original single hole, the net change is minus two holes closed.
Every remaining hole is exactly a named theorem with body `by sorry`.

## No longer needed

No published import is removed, and no existing module is withdrawn.
`lem-weil-pbc-noetherian-submodule-finite` is unnecessary for this route: over a
finite ring, finite terms have finite underlying sets, so cycles and their
quotients are finite directly. No claim is made that this node is globally
unreachable elsewhere in the project.

The other original dependencies remain in the plans of the extracted
coefficient triangle or local-complex calculations. In particular, K-flat
resolution, derived tensor descent, exact constant realization, the original
finite-perfect model predicate and exact slice restriction are retained. The
item's direct proof dependencies now name the four actual intermediate
statements its Lean proof uses.

## Where the brief, the DAG or earlier work was wrong

No published statement or definition was changed or disputed. The source read
was `literature/stacks-project/sites-cohomology.tex`, Tag 0942,
`lemma-bounded`, proof (1), together with Tags 094H and 094I. The unit's realized
statement and steps are unchanged.

A contractible-triangle shortcut was investigated and rejected: its required
successor homology input would assume the conclusion. None of that draft is
part of the delivery. The actual endpoints here are the coefficient kernel
tensor and the previous reduction restricted along the quotient.

The new statements have been checked mathematically for n=0 (the layer is
I/I^2), an empty chart or covering sieve, the zero coefficient ring, and a zero
complex. None requires a nonzero ring, nonempty cover or strict inequality
between the support endpoints. The local model predicate needs finite terms,
not projective layer terms: ordinary tensor of the projective residue complex
with the ideal layer need not itself remain projective.

Project source searches and the recorded Mathlib LeanFinder, LeanSearch, Loogle
and grep queries found general homology, exact-functor and triangle-of-a-short-
exact-sequence APIs, but no theorem with the actual completed coefficient and
prescribed local-model interfaces. The related `lem-sfb-adic-coefficient-filtration-triangle` works in the
constant-A coefficient model. It does not identify its reductions with the
actual completed-ring scalar reductions used here. The two strict-DVR sequence
nodes (`lem-sf-strict-dvr-coefficient-sequence` and
`lem-sf-strict-dvr-flat-tensor-sequence`) require a uniformizer and identify each
layer with the residue module; an arbitrary ideal layer need not have that form.
`lem-sfb-adic-graded-layer-constructibility` asserts constructibility without a
lower bound on a different constant-coefficient object.
`lem-sfb-coefficient-constant-tensor-local-models` gives local finite constancy for
a constant scalar tensor, without the required [a,b] support or completed-ring
comparison. `lem-weil-pbc-site-tensor-local-model-comparison` assumes finite-free
models for good truncations of both K-flat inputs, which are not the input models
here. `lem-weil-pbc-constant-coefficient-lisse-restriction` is an underived local
finite-module statement; it does not provide the actual complex/homology and
coefficient-isomorphism comparisons. These are related infrastructure, not
restatements of the extracted completed-coefficient comparison steps.

Blueprint searches for coefficient layers
and finite homology found no matching imported blueprint node. The ancestor
query for the existing item returned no attached blueprint ancestor.

## New nodes

`def-weil-pbc-finite-quotient-coefficient-layer-data` records actual kernel,
tensor and scalar-restriction constructions. Unlike the parent
`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`, it asserts neither
existence of a triangle nor any cohomological property.

`def-weil-pbc-finite-coefficient-local-homology-models` records the algebraic
local-complex predicate and ordinary constant realization. It differs from
`def-weil-pbc-finite-perfect-quotient-model-data`: its complexes need not have
projective terms, its object is arbitrary, and its comparisons concern homology
rather than a derived finite-perfect model of a reduction.

`lem-weil-pbc-finite-coefficient-local-homology-models` is the proved general
finite-ring homology and cover-descent calculation. Unlike the parent
`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`, it assumes an
arbitrary object's algebraic homology models and has no adic datum or triangle.

`lem-weil-pbc-finite-quotient-coefficient-layer-triangle` is the source's
coefficient short-exact-sequence step. Unlike the parent
`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`, it has no residue or
previous-model hypothesis, no coefficient-identification family, no support
interval, and no assertion about any homology sheaf.

`lem-weil-pbc-finite-quotient-layer-local-complexes` is the residue tensor
calculation, with no previous-model hypothesis or triangle conclusion. Unlike
`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`, its only endpoint
is the independently constructed kernel tensor. It supplies finite algebraic
terms and homology comparisons; the proved general theorem supplies finite
homology and global bounds.

`lem-weil-pbc-finite-quotient-previous-local-complexes` is the restriction-of-
coefficients calculation, with no residue-model hypothesis, layer calculation
or triangle conclusion. Unlike
`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`, its only endpoint
is the independently constructed restricted previous object. Its proof is
independent of the residue tensor calculation.

No shared-definition change record or forced adaptation is needed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
