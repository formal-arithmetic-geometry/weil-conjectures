## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_closedImmersion_fiber_support`
in `Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport`, with its signature,
visibility and public imports unchanged. Only this existing Lean module and its own DAG node
`lem-trf-finite-type-sheaf-fp-support` change.

The proof uses four proved private helpers: finite-subideal extraction with the same extended
ideal; the global-sections zero-locus preimage formula; the affine support formula; and the
closed subscheme/module construction for a finitely generated annihilating ideal.
The fibre is affine and Noetherian, so its extended annihilator has finite generators. Lift
those generators to the original annihilator to obtain J. The annihilator ideal-sheaf API
shows that F descends to V(J), and the exact canonical `pullback.map` in the statement has
range the inverse image of V(J). Support pullback and equality of the extended ideals finish.

Added proof imports of `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`,
`WeilConjectures.AlgebraicGeometry.AnnihilatorAffineBasicOpen`,
`WeilConjectures.AlgebraicGeometry.Modules.Annihilator`,
`WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
The supporting closed subscheme and H are real constructions, not choices from unfinished
existence theorems. The only choice of an adjunction is inside a theorem and is used solely
for the unique left-adjoint comparison isomorphism.

Validation: remote `lcompile.py` accepted the final file without warnings in 15.2 seconds.
All lines are at most 100 characters. The construction includes empty finite generator
families, the zero module and the zero fibre ring. No assumption is added and no target or
shared interface is changed. The blueprint unit route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_closedImmersion_fiber_support`
(node `lem-trf-finite-type-sheaf-fp-support`).

There are zero remaining textual sorries and zero added sorries. Nothing was split off.
The private helper theorems are all proved. Existing imported theorems retain their own
proof dependencies; this report does not claim to close their transitive holes.

## No longer needed

Removed these seven proof imports:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`

Removed these direct proof dependencies from this node:

- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-pushforward-tilde-spec`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-spec-module-tilde-sections`
- `lem-weil-pbc-tilde-pullback-base-change`

Explicit tilde/global-sections, tensor-product spectrum, affine pushforward and tensor/tilde
comparisons are unnecessary here: the existing annihilator and pullback-unit lemmas supply
the closed-subscheme construction, and `Scheme.Pullback.range_map` supplies the fibre image.
The finite-type affine-module criterion and tilde dictionary may remain transitive dependencies
of the imported source-library lemmas; no upstream declaration is removed or weakened, and
no globally pruned module is claimed. The top-level `tool_uses` entries for
`lem-weil-pbc-quasi-coherent-finite-type-affine` and
`lem-weil-pbc-tilde-pullback-base-change` are pruned from this node.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original affine algebra plan is valid but can be
implemented more directly using the existing proved `isIso_pullbackUnit_subschemeι_of_smul_eq_zero`
and `locallyOfFinitePresentation_subschemeι` APIs, rather than rebuilding the tilde
pushforward and quotient-module identifications. The updated DAG proof records this route.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
