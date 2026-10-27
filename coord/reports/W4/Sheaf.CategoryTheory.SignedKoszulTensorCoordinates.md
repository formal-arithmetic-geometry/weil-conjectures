## What changed

Replaced the proof hole of
`CategoryTheory.exists_ringedSignedKoszulTensorCoordinates` by a complete Lean reduction,
keeping its signature, public import, and existing definitions unchanged. Added two proof
imports, each containing one strictly smaller remaining theorem.

The assigned module now proves:

- The coefficient-complex contribution to the total differential, for arbitrary unbounded
  complexes, using `mapBifunctor.ι_D₁`, `d₁_eq`, inverse-unitor naturality and tensor interchange.
- The length-zero case of the coproduct property directly from the right unitor and the
  singleton cofan universal property, including the specified pure-tensor normalization.
- The length-zero second differential using total-tensor hom extensionality and
  `tensor_unit_d₂`.
- Construction of the coordinates from the universal property of the specified summand
  cofan, and the normalization and Kronecker projection identities.
- Projection of the unprojected differential equation, vanishing of mismatched erased
  subsets, and regrouping through the global-section scalar action into the exact
  conditional matrix formula of the assigned theorem.

The two remaining assertions concern positive tensor length only: the graded coproduct
property and the Koszul-direction differential on one canonical pure tensor. Neither
asserts the assigned coordinate theorem or takes its conclusion as a hypothesis. The
first has no differential assertion; the second has no coordinate isomorphism, no
universal property, and no coefficient-complex differential contribution. Their combination
with the proved pieces is written out in Lean.

All three modules were checked through `lcompile.py`. No shared definition, instance,
attribute, public import or existing declaration signature changed. No existing consumer
needs adaptation. The source-library boundary is preserved.

## Proved and sorry left

Existing hole replaced: `CategoryTheory.exists_ringedSignedKoszulTensorCoordinates`
(node `lem-cbc-signed-koszul-tensor-coordinates`). There are zero textual proof holes in the
assigned module. This is a decomposition, not a sorry-free proof of that theorem.

Exactly two holes added, each the entire proof of one public theorem in a new module:

- `CategoryTheory.isColimit_ringedNegativeKoszulSummands_succ`, in
  `Sheaf.CategoryTheory.SignedKoszulTensorCoproduct`, node
  `lem-cbc-signed-koszul-tensor-coproduct`.
- `CategoryTheory.ringedNegativeKoszulSummand_D₂_succ`, in
  `Sheaf.CategoryTheory.SignedKoszulSummandDifferential`, node
  `lem-cbc-signed-koszul-summand-differential`.

Thus one original hole was decomposed into two smaller holes (net +1); no unconditional
hole closure is claimed. All private helpers are proved. No data definition or private
lemma contains `sorry`.

The colimit proof is used only through its universal property; it determines the coordinate
comparison and its inverse uniquely with the specified normalization. No arbitrary object
is selected from a mere existence assertion.

## No longer needed

None. No existing imports, nodes or modules were withdrawn. Both new imports are used.
The original dependencies on the actual total tensor, sheaf tensor product and signed
Koszul model remain, and the parent node records both new proof dependencies. The unit
route is unchanged.

The nearby `RingedNegativeKoszulLowDegrees` theorem cannot supply these coordinates:
its proof uses `SignedKoszulFiniteCoordinates`, which imports this item. It was not
imported. The positive scalar-tower coordinate definitions and exterior-algebra Koszul
Leibniz lemmas describe different complexes and do not supply this normalized coproduct
or signed matrix; they were not added as dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or necessary interface repair was found. The declared proof dependencies
of this item provide the tensor and model definitions, rather than the two finite-coordinate
facts needed to finish the argument. The updated DAG distinguishes the coproduct fact from
the second-differential calculation, while the first-differential contribution and the
complete empty-tensor case are now proved directly.

LeanSearch returned HTTP 502 for both focused queries. This is recorded as unavailable,
without an absence verdict. LeanFinder, Loogle, the server source search and local searches
were available. They found the total-tensor and unitor infrastructure used in the proof,
but no matching noncircular finite-coordinate theorem.

The new statements were checked on the empty subset, a single selected factor, zero
coefficients, unit coefficients, the zero ring and empty sites. The singleton erased
coefficient is `(-1)^(q+1) * a₀^(m+1)`. The length-zero assertions were proved in Lean,
so neither remaining statement needs to assume or reconstruct that case. No scalar
inversion or boundedness hypothesis occurs.

## New nodes

`lem-cbc-signed-koszul-tensor-coproduct` states that the canonical summand cofan for a
positive-length ordered negative Koszul tensor is colimiting. It isolates the graded
finite free decomposition. Its source and full inductive proof are in its node and Lean
docstring. It has no claim about differentials, transitions or quasi-isomorphisms.

`lem-cbc-signed-koszul-summand-differential` states the unprojected second total differential
on a specified pure tensor for positive tensor length. It isolates the Leibniz calculation
with preceding-index signs and degree transports. It assumes no coordinates and asserts
no invertibility. Its node and docstring include the head/tail induction, scalar action
and edge cases. Projection and coefficient regrouping are proved in the assigned module.

No change record is needed: no existing statement or definition was changed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
