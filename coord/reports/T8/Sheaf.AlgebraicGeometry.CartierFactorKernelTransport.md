## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform_cartierFactor_kernel_transport`
without changing its statement. Private proved helpers establish finite generation of the product
ideal, the sectionwise description of a supported kernel, and transport of an included kernel
along a scheme isomorphism. The transported module is the actual pushforward of the product-centre
kernel. The normalized tensor adjunction supplies its inclusion and the required pullback
isomorphism, including their compatibility equation. The specified fibre-product map and normalized
composition comparison are constructed explicitly. The item node now describes this proof. New proof imports provide
`isFiniteType_toModules_sheaf`, `finite_sections_of_finiteType`, `isQuasicoherent_kernel`,
`isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`, and `ofFiniteType.mul`.
The generic tools `lem-pqf-finite-type-ideal-module` and
`lem-weil-pbc-quasi-coherent-finite-type-affine` are used only for the finite-generation
bridge in step 1; the unit has no competing ideal-module finite-generation lemma.
Quasi-coherent kernels and qcqs pushforward are already Lean-closed tools.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.Scheme.Modules.moduleStrictTransform_cartierFactor_kernel_transport`
(node `lem-trf-cartier-factor-kernel-transport`). Added zero holes. No `sorry` remains in the
item or any new declaration. Validation: the final file compiled cleanly through `lcompile.py` in 21.1 seconds.
The existing `moduleStrictTransform_properties` theorem supplies
quasi-coherence of the two kernels; its existing hole is unchanged.

## No longer needed

Removed the proof imports `WeilConjectures.Blowup.AdmissibleBlowup`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`. The last remains available through
necessary imports; no claim is made that it leaves the library's overall target closure.
All four public imports are unchanged.

The proof does not need `lemma-nagata-effective-cartier-is-invertible`: invertibility is already
the hypothesis `hJ`. It does not need `lemma-nagata-blowup-invertible-factor`: the blowup isomorphism
and its equation over the base are already hypotheses. It does not use
`lem-weil-pbc-module-pullback-quasi-coherent` for the transport: quasi-coherence follows directly
by pushforward along the scheme isomorphism. These three obsolete top-level tool approvals are
removed from this item's node; no unrelated approval is added. The statement dependencies and
the unit route remain intact. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan re-established invertibility and the blowup isomorphism although both
are supplied as inputs by the Lean statement. Its section-transport construction can be expressed
using pushforward and the normalized adjunction, which also proves the inclusion equation by
counit naturality and the triangle identity. No mathematical statement or definition repair was
needed. Edge cases include empty schemes and opens, zero and unit ideals, and modules with
Cartier-supported torsion; none of the proof steps assumes such torsion vanishes.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
