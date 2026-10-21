## What changed

Proved `AlgebraicGeometry.Scheme.pbc_adic_reduction_cohomology_sequence` with its
original signature. The proof constructs the coefficient short exact sequence by
exact constant sheafification and flat completed scalar extension, using the actual
constructed unit and finite-reduction isomorphisms. Their generator formulas show
that the quotient map sends 1 to 1.

Added `Sheaf.Paper.AdicReductionTriangle`, containing the proved generic theorem
`AlgebraicGeometry.Scheme.pbc_adic_reduction_triangle`: a normalized two-term
coefficient resolution gives the distinguished derived scalar-extension triangle,
the tensor-multiplication action on cohomology, and its ordinary cokernel comparison.
Its proof uses a flat-term K-flat resolution and Mathlib's triangle of a short exact
sequence. Private tensor/sheafification helpers adapt the corresponding arguments
of `Sheaf.Paper.DerivedReductionResolutionIndependence`, without its unused
sections-exact hypothesis. The assigned theorem then obtains the requested short
exact sequence from three consecutive homology exactness statements and the
ordinary adjunction identity. All new helpers are private and proved.

The original public imports stay unchanged. Added only proof imports to the item;
the new module exposes only the imports needed by its statement. Updated both DAG
proof records to describe this implementation. No existing definition or statement
was changed, and no other group's module was adapted.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.pbc_adic_reduction_cohomology_sequence`.

Added zero holes. The new theorem
`AlgebraicGeometry.Scheme.pbc_adic_reduction_triangle` and every private helper in
both delivered modules have complete proofs. There are zero `sorry`s in either
module. This is a proof of the item, not a decomposition into unfinished statements.
The existing library dependencies are used as stated; no stronger axiom is added.

Both modules passed `lcompile.py --all` with no errors or warnings.

## No longer needed

The following original direct proof dependencies are unnecessary on this route and
were removed from the item's `proof_deps`, proof-step `uses`, and old `tool_uses`:

- `lem-pc-bounded-above-flat-kflat-site`
  (`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`): use an arbitrary flat-term
  K-flat resolution directly, with no bounded-above argument.
- `lem-pur-derived-change-of-rings`
  (`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`): use the normalized
  scalar adjunction and K-flat counit API already provided by
  `Sheaf.Paper.BoundedConstructibleTower`.
- `lem-weil-pbc-constant-module-section-properties`
  (`Sheaf.Paper.ConstantModuleSectionProperties`): exactness of constant module
  sheafification and the actual tensor-generator formulas suffice; no exactness
  claim about sections on each object is used.
- `lem-weil-pbc-site-derived-tensor-descent`
  (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`):
  tensor the coefficient sequence degreewise on a K-flat model and use the
  short-exact-sequence triangle directly.

No original import was removed from the assigned file, and no Lean module is
withdrawn. The list concerns this proof's direct dependencies; it does not claim
that modules still used transitively elsewhere can be deleted. The final new
module imports none of these four modules directly. Temporary proof imports of
`CompletedConstantSheafReduction`, `ExtensionIntegersDvr`, and
`ConstantModuleSectionProperties` were also removed
from the new triangle module after its proof was generalized.

## Where the brief, the DAG or earlier work was wrong

The proof plan is valid, but it does not require building a separate bounded-above
K-flat two-term complex or invoking the full derived tensor descent theorem.
The existing normalized scalar-adjunction API identifies the short exact sequence
triangle directly. In particular the proof imposes no boundedness, constructibility,
or cohomological flatness hypothesis on the complex.

No statement repair, withdrawal, forced adaptation, or change record is needed.
The unit's integral-truncation route and the assigned statement are preserved.

## New nodes

`lem-weil-pbc-adic-reduction-triangle`, in
`dag/nodes/sec-smooth-base-change/lem-weil-pbc-adic-reduction-triangle.json`, records
the generic two-term quotient triangle before the long exact cohomology argument.
The associated new module is fully proved in this delivery; it leaves no work for
another group. Its statement applies to any normalized coefficient short exact
sequence, while the assigned theorem constructs that sequence specifically for
completed finite-extension DVR coefficients and takes its cohomology sequence.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
