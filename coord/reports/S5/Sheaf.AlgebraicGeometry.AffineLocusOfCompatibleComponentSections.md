## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_locus_of_compatible_component_sections`
in `Sheaf.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections`, with its signature
and public imports unchanged. The proof follows the existing four-step DAG plan:
obtain the open nonvanishing locus, identify its inverse images using the component
isomorphisms and `nonvanishing_tensorPullback`, apply
`isAffine_of_finite_closed_cover` to the restricted closed immersions, and transport
the section through the inverse right unitor to `L.tensorPow 1`.

The existing proved helper `nonvanishingLocus_iso` is accessed by a proof-only
`import all WeilConjectures.AlgebraicGeometry.AmpleIso`; the old `Sheaf` wrapper
re-exports only the public upstream interface and cannot expose that private helper.
No statement, definition, or DAG route changes; no additional modules or nodes.

Validation: the complete proof compiles through `lcompile.py` without warnings.
The construction uses the existing cover theorem for every `r`, including zero:
when `r = 0`, the covering hypothesis forces the ambient scheme to be empty.
There is no nonemptiness assumption on the locus, the components, or `T`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.affine_locus_of_compatible_component_sections`
(node `lem-sc-affine-locus-compatible-component-sections`).

Added 0 holes; split off 0 statements. There are 0 remaining `sorry`s in the
delivered module. Imported declarations retain their existing proofs and dependencies;
this delivery does not claim to discharge their transitive obligations.

## No longer needed

Removed these redundant proof imports:

- `Sheaf.AlgebraicGeometry.AmpleIso`: replaced with the upstream `import all` required
  to access its already proved nonvanishing-isomorphism helper.
- `Sheaf.AlgebraicGeometry.NonvanishingTensorPullback`: retired re-export wrapper;
  the direct upstream import remains.
- `Sheaf.Paper.NonvanishingSectionTrivializes`: retired re-export wrapper;
  the direct upstream import remains.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: already publicly available
  through the existing `Ample` statement import.

No declared DAG proof dependencies are pruned: each geometric step of the existing
plan is used. No underlying mathematical modules or unit steps are bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned statement and its four-step plan are valid and suffice unchanged.
The old `import all Sheaf.AlgebraicGeometry.AmpleIso` targets a retired wrapper,
so it does not expose the upstream private `nonvanishingLocus_iso` helper; importing
its actual upstream module resolves that proof-environment issue. The first compiler
attempt also required `erw` for the definitionally equal `Hom.app`/`val.app` section
presentations, and explicit underlying points for open-subscheme coercions.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
