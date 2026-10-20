## What changed

Completed all three remaining proofs in
`Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: affine chart equations, the
frame-induced affine-space isomorphism including its zero section, and invertible
transition matrices with their coordinate formula. The proofs work for arbitrary
framed opens, including empty opens and rank zero. Added private proof imports
`Mathlib.LinearAlgebra.Matrix.Basis` and
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`.

Profiling identified expensive conversions through the large existential used by
`antiEquivalence`. Constructed `structureAlgebraFunctor` explicitly on objects and
section maps, proved `structureAlgebraFunctor_isEquivalence` by a natural
isomorphism to the characterized relative-spectrum functor, and used its genuine
quasi-inverse. The geometric calculation then uses the equivalence API with local
irreducibility. The complete item compiles cleanly (31.8, 47.8 and 47.0 seconds in
separate checks). No existing public signature or public import changed. The
choice of quasi-inverse can change, but the projection, algebra identification,
augmentation, charts and coordinates retain their relative-spectrum meanings up
to the unique algebra-compatible isomorphism. Target meaning review is reopened.

The now-concrete functor makes the object-equality casts in `algebraIso` and
`ReesConeNormalization.coneAlgebraIso` unnecessary. Adapted the two private
object/map proofs and the final simplification in
`ConormalConeZeroSectionPullback`. These are the only adapted consumer modules;
both were unclaimed. The adapted conormal proof and the unchanged normalized-cone
existence proof compile cleanly in 7.6 and 13.5 seconds. Also checked the normal
bundle, vector direct sum, section deformation, integration-mate and vector-bundle
target consumers against the replacement interface. All fourteen consumer checks
passed, including every direct importer and the additional declaration users.
The unchanged normalized-cone existence module was checked as well.

Updated the existing definition node's proof narrative, origin and Lean attachment
to include the concrete functor and its proved equivalence property. Its dependency
set and the blueprint unit route are unchanged. Also updated the affine-equations
node to record the scalar and augmentation calculation. No file under `WeilConjectures`
was changed. Change records:

- `coord/changes/N3-vector-bundle-antiEquivalence.md`
- `coord/changes/N3-vector-bundle-algebraIso.md`
- `coord/changes/N3-vector-bundle-coneAlgebraIso.md`

## Proved and sorry left

Closed all three original holes:

- `AlgebraicGeometry.VectorBundleZeroSection.affineChart_equations`
  (`lem-asd-vector-bundle-affine-chart-equations`).
- `AlgebraicGeometry.VectorBundleZeroSection.trivializationMap_spec`
  (`def-asd-vector-bundle-zero-section`).
- `AlgebraicGeometry.VectorBundleZeroSection.transition_spec`
  (`def-asd-vector-bundle-zero-section`).

Holes closed: 3. Holes added: 0. Sorries left in the item: 0.
The two adapted consumers also contain no sorry. All added helper statements are
proved; no unfinished statements were split off.

## No longer needed

None. No existing import, dependency node or module was removed. The proof retains
the unit's relative-spectrum, affine comparison, frame and transition-matrix route.
The adopted source library's private structure-algebra functor remains untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was false or weakened. The original chosen-functor
representation was too expensive to reduce in the completed proof, requiring the
representation repair documented above. The node's former unfinished
trivialization and transition steps are now completed.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ReesConeNormalization` (unclaimed): the original line 45
fails with `Application type mismatch` at `eqToIso`: the old chosen functor's object
equality has a different source from the new inverse counit. Removed only that
obsolete cast from `coneAlgebraIso` (old lines 44–46). Its signature and all other
declarations and imports are unchanged.

`Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback` (unclaimed): original
lines 80 and 92 fail with `Type mismatch` because the source theorem describes the
old chosen functor, while the goals describe the concrete functor. Replaced the
private object proof by `rfl` and the private map proof by cancellation of reflexive
casts followed by `rfl`. Original line 165 also fails after simplification because
its term retains a reflexive object-equality cast absent from the new
`coneAlgebraIso`; added `eqToHom_refl` and `Category.comp_id` to that simplification.
Every signature stays identical. These edits are necessary for the new interface;
no additional proof or statement was changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
