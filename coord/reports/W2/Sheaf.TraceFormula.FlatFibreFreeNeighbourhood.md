## What changed

Filled `AlgebraicGeometry.Scheme.Modules.exists_free_neighbourhood` in
`Sheaf.TraceFormula.FlatFibreFreeNeighbourhood`, preserving its signature and public imports.
The proof uses the existing finite-presentation stalk/fibre data theorem, transports fibre
flatness through its compatible ring and additive equivalences, applies the closed-fibre
flatness criterion to R -> B -> B, and spreads a finite basis of the resulting free stalk.
The subsingleton stalk is free directly; the same basis-spreading theorem covers rank zero.
The existing scheme over-site and free-restriction isomorphisms give precisely the requested
restriction of the ambient free sheaf. Only this module and its own DAG node change.

Validation: `lcompile.py` compiled the final module cleanly in 9.4 seconds.
Import-direction checks for both newly used Sheaf dependencies passed.

## Proved and sorry left

Closed 1 of 1 textual holes:
`AlgebraicGeometry.Scheme.Modules.exists_free_neighbourhood`
(`lem-trf-flat-fibre-free-neighbourhood`). No sorry remains in the item and no holes were added
or split off. The proof uses the already stated, still unproved dependencies
`AlgebraicGeometry.Scheme.Hom.exists_finitePresentation_stalk_fibre_data` and
`AlgebraicGeometry.RingedSpace.exists_free_neighbourhood_prescribed_stalk_basis`; this is a
proof from the DAG declarations, rather than a claim that their transitive holes are closed.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`
- `WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`
- `WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk`
- `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
- `Sheaf.Paper.DerivedHomMayerVietoris`

The first and fourth are encapsulated in the stalk/fibre data declaration; the kernel and
surjectivity arguments are encapsulated in the prescribed basis-spreading declaration.
`DerivedHomMayerVietoris` is already exported by that declaration's module. These modules
remain needed transitively, so this is removal of redundant direct imports, not withdrawal.
The node's direct dependencies `lem-weil-pbc-nakayama-local-generators` and
`lem-weil-pbc-module-finite-type-surjective-on-stalk` are unnecessary: split directly on
subsingleton versus nontrivial M, and spread its finite basis in both cases. The latter
lemma remains a dependency of basis spreading. Removed obsolete top-level tool-use entries
for the direct surjectivity, kernel, fibre-quotient and pullback-stalk arguments; retained
the closed-fibre criterion approval. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement or source error. The DAG's zero-residue-fibre step is longer than necessary:
the zero stalk already has a finite empty basis, so the same prescribed-basis theorem proves
its conclusion. The compatible quotient data in the new dependency has exactly the scalar
formula needed for `Module.Flat.semilinearEquiv_iff` (existing node
`lem-pc-flat-semilinear-equiv`), used here as a general algebra transport tool.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
