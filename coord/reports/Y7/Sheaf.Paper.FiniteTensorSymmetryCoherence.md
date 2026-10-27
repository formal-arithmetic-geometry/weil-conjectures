## What changed

Proved `WeilConjectures.PurityFiniteSetting.finiteTensorSymmetryCoherence` by a
native K-flat representative argument. Private proved helpers instantiate the proved localization-braiding theorem,
identify its invertible K-flat tensor comparisons, and give a
categorical diagram chase for the representative normalization. The canonical
scalar-extension representative is natural and invertible on K-flat complexes
by the existing exact-right-adjoint theorem. The source library supplies the
ordinary scalar-extension symmetry equation and its signed cochain version.
Transport along K-flat representative isomorphisms handles arbitrary objects.
The assigned public signature and existing definitions are unchanged.
The final module compiled through `lcompile.py` in 53.4 seconds, below the
60-second per-file limit; the source signature was checked verbatim.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.finiteTensorSymmetryCoherence`.
No holes added; no `sorry` remains in the delivered module. The existing
`existsUnique_finiteTensorCore` normalization theorem remains a dependency
through `finiteTensorCore`; this delivery does not claim to prove it.

## No longer needed

The following original planned proof dependencies are unused by this proof:

- `det-sp-scalar-extension-functor`
- `lem-sf-reduction-flat-model`
- `lem-pc-kflat-resolution`
- `lem-pur-kflat-change-of-rings-independent`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-pur-cochain-pullback-tensor-coherence`
- `lem-pur-cochain-comparison-monoidal-equations`

The native source-library K-flat resolution and localization API, the proved
localization-braiding and exact-right-adjoint representative theorems, and the normalization in
`FiniteTensorSignedReduction` suffice. The scalar-extension symmetry and its
signed total-complex equation are already proved in the source library.
No module is withdrawn: these nodes can still be needed by other arguments or
by the construction of the normalized tensorator. No original public import
is removed. Redundant private imports of `LeftDerivedFunctor.MonoidalStructure`,
`DerivedCategory.FlatModel`, and `Monoidal.MapHomologicalComplex` were removed:
the used `ExtendScalars.Trace` module already imports these APIs.

## Where the brief, the DAG or earlier work was wrong

The first original proof step calls ordinary scalar extension exact for an
arbitrary coefficient quotient. Such a quotient need not be flat. This proof
uses exactness of restriction of scalars instead, and applies scalar extension
only to K-flat representatives. It neither assumes nor proves flatness of the
quotient. The broad constructibility and Tor-interval statements of the
original route are unnecessary for this ambient symmetry square.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
