## What changed

Proved `WeilConjectures.PurityFiniteSetting.cartier_relative_boundary_realization` in
`Sheaf.Paper.CartierRelativeBoundaryRealization`, preserving its signature and all existing public imports. Replaced the result type
annotation of `cartierRelativeCoefficientBoundary` by its definitionally equal native
module-sheaf Ext annotation; its defining value is unchanged. Added proved private helpers for module restriction
surjectivity, evaluated comparison quasi-isomorphisms, the relative cone quasi-isomorphism,
restriction epimorphisms after extension by zero, and the normalized cone/kernel square.

The augmented lift uses `InjectiveResolution.descOfQuasiIso` on the exact scalar-forgetting
image of the module resolution. Existing evaluation acyclicity and acyclic-resolution
comparison prove both section maps are quasi-isomorphisms. A morphism of mapping-cone
triangles proves that the actual shifted cone map is a quasi-isomorphism. Both normalized
kernel inclusions and their strict square remain explicit. Homotopy of augmented lifts,
together with the existing relative-section homotopy construction, proves equality of the
localized maps.

The residue root map uses `residueFiniteRootMap_isIso`. Existing Cartier scalar-adjunct
specifications prove both full supported boundary equations. Uniqueness of the normalized
general divisor family proves the last equality. These are equations of supported classes;
no passage to an unsupported ordinary class or a local representative is used.

Proof-only `import all` imports reuse existing proved private helpers in
`CartierReductionSiteComparison`, `PurityRelativeCone`, `RelativeTorsorCohomology`, and
`ModuleAbelianDerivedDirectImageComparison`. The item node's proof, proof dependencies,
proof origin and obsolete tool approvals are updated to match the proof.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.cartier_relative_boundary_realization`
(node `lem-pur-cartier-relative-boundary-realization`).

No holes added, no statements split off, and no `sorry` remains in the delivered module.
Imported existing theorem holes, including the normalized general divisor-family existence,
are unchanged and remain their own assigned items. This delivery proves the item from the
existing library declarations; it does not claim to close their transitive holes.

## No longer needed

The proof does not use the planned theorem
`lem-pur-module-restriction-kernel-comparison`: direct evaluation acyclicity and the
mapping-cone triangle give the cone isomorphism before constructing the kernel square.
Its proof-only import is removed. Both kernel inclusions and the kernel square remain.

The planned invocations of `lem-sc-line-bundle-torsor`,
`lem-asd-finite-etale-twist-line`, `lem-amb-closed-support-hom`,
`lem-asd-supported-kummer-support-hom-naturality`, and
`lem-amb-relative-torsor-forget-normalization` are unnecessary in this proof: the existing
Cartier boundary and normalized scalar adjunct already retain the torsor, section, sign,
and full supported Ext equation. The corresponding unused proof-only imports are removed.
Existing public imports and declaration names are preserved; this is not a claim
that these nodes can be withdrawn globally or from their other consumers.

Removed proof-only imports:
`Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
`Sheaf.CategoryTheory.ModuleRestrictionKernelComparison`,
`Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`, and
`Sheaf.AlgebraicGeometry.RelativeTorsorForgetNormalization`.

No module is withdrawn. The unit's statement and proof route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's longer route is not needed for the existing Lean statement. Its module already
defines the two boundaries using `cartierReducedEtale`, whose defining specification is
precisely the supported scalar-adjunct equation. The final divisor equality follows from
uniqueness of the existing normalized general divisor family. Also, both evaluated maps
being quasi-isomorphisms already imply the cone map is one by the mapping-cone triangle;
there is no need to establish the kernel comparison first.

The result annotation repair is recorded in
`coord/changes/cartier-relative-boundary-coefficient-type.md`. Its original selected-site
wrapper forced expensive comparison of native and wrapped derived-localization structures.
The native annotation and synchronous elaboration allow the complete file to compile in
52.4 seconds under the unchanged 60-second limit. The defining term, mathematical endpoints,
and item theorem statement are unchanged. Source search and `tools/downstream.py --uses`
find no external consumer. No target definition or statement changes meaning.

The proof handles empty support and empty
ambient scheme, nonreduced Cartier divisors, positive coefficient level one, and ramified
coefficients without additional assumptions. Restriction surjectivity uses injectivity in
the module category, and evaluation acyclicity uses the existing forgetful comparison;
it never asserts that a forgotten injective module sheaf is injective as an abelian sheaf.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
