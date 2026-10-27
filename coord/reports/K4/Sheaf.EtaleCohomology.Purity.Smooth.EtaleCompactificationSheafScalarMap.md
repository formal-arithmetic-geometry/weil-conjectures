## What changed

The assigned module now constructs the required isomorphisms by proving that its specified
compactification graph maps are invertible. Properly supported sections identify every
compactification with the same subfunctor of direct image; Zariski main theorem supplies a
finite compactification for which the existing finite-comparison theorem applies.

The scalar map is the canonical isomorphism from uniqueness of the two composite left adjoints
for literal restriction and scalar restriction, which commute definitionally.
It is constructed privately to avoid importing the parent computation module.
Private helpers compute its unit, compare the ordinary counit mate and open scalar map with inclusion in direct image,
and verify the formula on arbitrary local coefficient sections using the actual sheaf tensor
structure. The main theorem combines these calculations. Existing public statements and
definitions are unchanged. The public import reduction is documented in
`coord/changes/K4-etale-compactification-scalar-imports.md`; its only direct consumer
is `EtaleSheafFoldScalar`, which requires no source adaptation. The node copy records this adjunction and proper-support route.

Repair of return d5f22ae9c: removed the private duplicate `cached_sheafify`. The proof now
privately imports `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` and registers its existing
`AlgebraicGeometry.Etale.supportedHasSheafify` as a local instance. Its binders and conclusion
are exactly those of the removed cache. The import-direction check confirms no cycle.

Validation: the repaired full assigned module compiled through `lcompile.py` with its normal
options in 51.5 seconds, with no errors or warnings. No temporary profiling or heartbeat options
are present in the delivered module. The delivery checks validate the consumer interface.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleCompactificationSheafScalarMap`
(node `lem-sp-etale-compactification-sheaf-scalar-map`), the only original hole.

Actual count: 1 of 1 original holes proved; 0 holes remain; 0 holes added; 0 split off.
All private helpers are fully proved. The proof uses the existing declared proper-support
and finite-compactification results, whose own proofs are outside this packet.

## No longer needed

Removed private imports:

- `Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap`;
- `Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction`;
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.

The proof no longer calls `lem-pur-etale-sheaf-projection-map`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison`,
`lem-sfb-site-inverse-image-bilinear-adjunction`, or
`lem-pc-sites-module-sheafification-tensor`. Its local formula follows from the scalar
adjunction unit and lax monoidal identities, so neither a general bilinear adjunction
package nor generation after sheafification is required. The derived compact-support
normalization theorem `lem-asd-etale-compact-support-normalization` is replaced in the proof
by its ordinary graph normalization and the finite compactification comparison.
`lem-coef-etale-open-tensor` is not called: the ordinary open comparison is computed from
its definition and adjunction units. These six obsolete cross-unit `tool_uses` entries
are removed in the node copy. Public imports now use `EtaleCompactificationGraphMap` and `EtaleOpenTensorDefs`
directly in place of `EtaleCompactSupportNormalization` and `EtaleOpenTensor`. The unused public
imports `EtaleInverseImageModulesExact`, `CochainTensorUniverses`, and
`RingedTopoiInverseImageTensorComparison` are removed. All statement dependencies remain;
none of these declarations or modules is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned generic inverse-image tensor/bilinear lemmas do not directly match the fixed
constant-coefficient adjunctions used by this statement. They are unnecessary: mate
calculus computes the specified ordinary arrow, and the lax monoidal sheaf tensor
structure computes arbitrary local coefficient sections. No statement correction is
needed. The scalar isomorphism is constructed here from adjunctions rather than imported from
`EtaleSumCoefficientComputation`, whose future proof uses this item. The proof uses the
existing proper-support composition and finite compactification nodes as tools to establish invertibility of the prescribed graph maps; it does not
choose unnormalized comparison data. No blueprint unit statement or realized step is bypassed. The unit record has no attached
realization for this step, and each new proof dependency was checked for a path back to this item;
none has one.

The previous duplicate sheafification cache violated the one-statement rule; this repair
uses the existing theorem instead, exactly as the return requests. No new theorem or node
is needed for this instance reuse.

The resumed launcher metadata has start `1792769010.1855807`; the earlier session
recorded `1792759095`. I did not edit `.budget` and continued the same proof packet.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
