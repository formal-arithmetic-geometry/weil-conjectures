## What changed

Filled `AlgebraicGeometry.Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators`
without changing its signature, public imports, or definitions. Only the item module and its
DAG proof record change, in addition to this report.

The forward implication shrinks the smooth neighbourhood to one of constant relative
dimension. The proved finite locally free differential theorem supplies a frame whose germs
form a stalk basis. Two proved private helpers transport its spanning family through the
semilinear restriction comparison. A pullback square and the proved smooth relative dimension
API compute the dimension of the open fibre. Flatness descends across the open-immersion stalk
isomorphism.

The reverse implication imports and uses the three declared affine comparison dependencies:
`exists_affineChart_stalk_differentials`, `affine_fibre_point_dimension`, and
`KaehlerDifferential.FibreLocalization.comparison`. It identifies the fibre prime by the inverse
of `PrimeSpectrum.preimageEquivFiber`, transports the finrank bound using the specified tensor
commutativity action, and applies the two existing ring smoothness criteria. Mathlib's
`smoothLocus` and `formallySmooth_stalkMap_iff` finish the passage to a neighbourhood.

All added imports are private proof imports. The DAG proof, proof dependencies, and proof
origin follow this implementation; the two obsolete direct tool-use entries are removed.
The unit route is unchanged. No source-library module is modified.

Static checks confirm the original theorem signature and public import list are identical,
all lines satisfy the 100-character limit, and no holes or forbidden declarations occur
in the item. The updated proof dependency graph has no cycles. The final single-file remote
compile passed cleanly in 13.2 seconds (exit code 0, no warnings).

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators`
(node `lem-trf-smooth-at-point-differential-criterion`). Added zero holes and zero split-off
statements. The item module has zero `sorry`s remaining. Both private helpers are proved.

The three imported affine comparison declarations retain their existing holes in their own
modules; this delivery neither edits nor duplicates them. Thus the result is a complete proof
from the project's declared dependencies, not an assertion that its transitive axiom closure
is already sorry-free.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.RingTheory.Kaehler.TensorProduct`
- `WeilConjectures.RingTheory.SingularIdeal`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `WeilConjectures.AlgebraicGeometry.Thickening`
- `WeilConjectures.AlgebraicGeometry.FormallySmooth`

The following old direct proof dependencies are no longer used:

- `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`: use the proved finite locally
  free differential API on a neighbourhood of constant relative dimension instead.
- `lem-weil-pbc-affine-open-stalk-localization` and
  `lem-weil-pbc-spec-tilde-stalk-localization`: the affine chart comparison encapsulates the
  reverse stalk comparisons; the forward proof takes germs of an existing local frame.
- `lem-weil-pbc-principal-localization-open-immersion`,
  `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, and
  `lem-weil-pbc-smooth-restrict-open-subschemes`: the reverse conclusion uses the existing
  smooth-locus API directly.

The Mathlib proof APIs that remain used are already supplied by the preserved public imports.
These are direct dependency removals. No module is withdrawn, no upstream declaration is
removed, and no claim is made that another consumer no longer needs any of these nodes.
The affine-opens induced-ring-map square remains needed by the affine fibre comparison.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The module's inherited private imports did not yet include the
three affine comparison modules already named by the current DAG; they are now imported and
used. The older six-step docstring describes the source argument; the updated DAG records the
shorter geometric assembly through the proved stalk-frame and smooth-locus APIs.

Checked the source at Stacks Morphisms, `lemma-smooth-at-point` (01V9), and
`lemma-smooth-omega-finite-locally-free` (02G1). The proof uses the neighbourhood dimension of
the fibre throughout, including at nonclosed points. The span transport and tensor dimension
bound also cover zero generators. The theorem introduces no extra assumptions and retains
all scheme and ring universes.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
