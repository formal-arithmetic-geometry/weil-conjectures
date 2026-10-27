## What changed

The existing declaration `AlgebraicGeometry.stacks_nodal_closed_subcurve` has its original
signature and public imports, with a complete Lean proof combining the local cases and
retaining the scalar equations in every transported completion. No source-library file,
definition, existing public interface, or target statement was changed.

Six new statement modules isolate genuine reusable parts of Stacks Tag 0E38. Five are
proved: complementary-boundary finiteness, finite reduced discrete residue-field coproducts,
scalar-compatible split-node completion transport, the local smooth/node dichotomy, and
smoothness from a regular stalk with separable algebraic residue field. The sixth contains
the remaining completed component-ideal calculation, restricted to a single boundary point.
The original node and six new nodes record these dependencies. No change record is required:
there is no existing statement or definition repair and no adapted consumer.

All seven modules compile together with no errors or warnings. The original theorem
signature was compared textually and is unchanged. Every new statement was checked at the
empty-scheme, whole-subcurve, single-axis, both-axes, irreducible self-node, nontrivial
separable residue-field, and characteristic-two cases as applicable. In the local-rings
statement the boundary hypothesis rules out both whole-subcurve and irreducible self-node
cases; it needs neither global nodality nor a scalar-compatible completion.

## Proved and sorry left

Original holes: 1. Closed original hole:
`AlgebraicGeometry.stacks_nodal_closed_subcurve` (0 sorry left in the item).

Added holes: 1, exactly
`AlgebraicGeometry.split_nodal_boundary_local_rings`, node
`lem-trf-split-nodal-boundary-local-rings`, in
`lean/Sheaf/AlgebraicGeometry/SplitNodalBoundaryLocalRings.lean`.
Its entire proof is `by sorry`; there is no sorry in any definition or private helper.

This is a decomposition (one original hole closed, one strictly smaller hole added),
not a net hole closure. The remaining result is only the source's boundary local-ring
calculation. It makes no global nodality, inheritance, finite-discreteness, separability,
smooth-neighbourhood, coproduct, or k-scalar transport assertion. Its two conclusions
come from the same identification of the two completed component kernels with the axes.

Fully proved new public declarations:
- `AlgebraicGeometry.complementary_pure_subcurve_boundary_finite`
- `AlgebraicGeometry.finite_reduced_discrete_residue_fields`
- `AlgebraicGeometry.regular_separable_residue_smooth`
- `AlgebraicGeometry.split_node_completion_transport`
- `AlgebraicGeometry.split_nodal_subcurve_local_dichotomy`

The original theorem now follows by actual Lean case analysis, isomorphism transport,
residue-field compatibility, and coproduct construction. The local-ring result retains
the original plan's faithful-flat completion, reduced completed component quotients,
three-prime classification, contraction of the sum ideal, and regularity descent. Its
source and complete proof in words are in its docstring and node. I did not claim those
unwritten steps proved. Existing imported declarations that themselves have sorry are
unchanged and are not additional holes introduced by this packet.

## No longer needed

The direct proof imports removed from the item are:
- `WeilConjectures.FieldTheory.SeparableExtension`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`
- `Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents`
- `Sheaf.TraceFormula.CurveNormalizationCompletion`
- `Sheaf.TraceFormula.ReducedSchemeImage`
- `WeilConjectures.RingTheory.CompletionRegularLocal`
- `WeilConjectures.RingTheory.LocalCompletionQuotient`
- `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`
- `Mathlib.RingTheory.AdicCompletion.LocalRing`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`

`Mathlib.AlgebraicGeometry.Noetherian` remains a proof import.
The component-union and reduced-image modules remain used by the proved helpers.
The completion, regular-domain, power-series, minimal-prime, radical and contraction
inputs remain needed transitively or in the remaining local-ring proof; they are not
claimed pruned merely because the parent delegates their calculation.

The route no longer needs node `lem-sc-zero-dim-noetherian-finite-discrete`, module
`Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`: a direct finite union
of finite distinct-component intersections gives finiteness, then ambient closed points
give discreteness. It also no longer needs the custom separable-extension detour
`def-weil-pbc-separable-field-extension` / `WeilConjectures.FieldTheory.SeparableExtension`
or `lem-weil-pbc-regular-local-separable-residue-smooth` /
`WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth` for this argument:
the proved upstream formally-smooth-residue criterion applies directly to separable
algebraic residue fields. These dependencies may still serve unrelated library users;
no adopted-source declaration was removed.

The smooth-point proof uses the proved scheme-level
`Smooth.isRegularLocalRing_stalk`, rather than importing
`Sheaf.RingTheory.SmoothOverFieldRegularLocal` directly; regularity itself remains an
input. No claim is made to prune that mathematical fact. No module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement and its source are correct. The planned general separable-extension
conversion is unnecessary: separable algebraic extensions are formally etale, and the
upstream local smoothness theorem uses formally smooth residue fields directly.
The zero-dimensional-scheme theorem is also unnecessary for the finite-type boundary.
The unit `sk-i-curve-zero` has empty realized lists; its statement and route were preserved.
No upstream statement exception, quarantine withdrawal, or forced consumer adaptation is used.

## New nodes

`lem-trf-complementary-pure-subcurve-boundary-finite` is the proved finite/discrete boundary
step, independent of nodality. Its statement explicitly includes the ambient Jacobson
hypothesis used for closed points.

`lem-trf-finite-reduced-discrete-residue-fields` is the proved canonical coproduct argument,
including the structural equations over the ground field and the empty coproduct.

`lem-trf-split-node-completion-transport` is proved for arbitrary local rings and compatible
scalar maps. No finite-type hypothesis or arbitrary data choice is used.

`lem-trf-regular-separable-residue-smooth` is the proved scheme bridge from the regular-local
criterion. Its residue-field equivalence respects the canonical base embedding; the proof
checks this through germs rather than changing the algebra structure in the statement.

`lem-trf-split-nodal-boundary-local-rings` is the sole unfinished source lemma: regularity
of the selected branch and field stalks on its intersection with the complementary closure.
Its proof words retain the necessary reducedness of completed component quotients, excluding
unjustified identification of arbitrary completed quotient maps with the axes.

`lem-trf-split-nodal-subcurve-local-dichotomy` is proved from the boundary-local-rings lemma,
the proved smoothness bridge, and the existing complementary-component and reduced-image
results. Away from the complementary image, a surjective reduced closed immersion gives
local agreement; in the smooth case a connected open with domain stalks is irreducible.

Each new node has three recorded kinds of actual Mathlib searches and the matching Lean
signature. No new node merely renames the original theorem, and none bypasses the unit route.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
