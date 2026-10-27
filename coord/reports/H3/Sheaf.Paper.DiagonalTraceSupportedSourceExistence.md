## What changed

Replaced the proof hole of `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_supportedSource_exists` by an ordinary normalized section comparison and a direct proof of derived acyclicity. The public statement and original public import are unchanged. All added declarations are private helpers with complete bodies in the item module.

The coefficient comparison is the actual limit map, not a chosen alternate coefficient identification. Its invertibility and composition/identity equations follow from the finite residue-ring projections. The existing tensor composition theorem and the generic identity helper from `CompletedOrdinaryComparisons` supply module isomorphisms whose underlying additive maps are the prescribed canonical comparisons.

For acyclicity, diagonal pushforward is exact and has an exact left adjoint, so it sends a K-injective resolution to a quasi-isomorphism with K-injective target. Its composite with the projection is naturally the identity. Naturality of the given derived unit and its computation on K-injectives therefore prove that the unit is invertible on the supported source, including the single-complex comparisons used in `diagonalTraceRightSingle`.

A named equality identifies the published completed source with diagonal pushforward of the unit; component comparison lemmas identify the scalar-restriction forgetful composite with the ordinary module forgetful functor. The source isomorphism stores the first equality as explicit transport; its normalization uses a generic proved lemma for the image of an equality transport. These interfaces avoid repeated kernel conversion of large module actions. Profiling identified expensive kernel conversions between private abbreviations and their expanded public expressions. Whole-functor equality was replaced by component comparisons, and the forgetful functor and unit expressions now match throughout the helpers. This removes repeated large module-action conversion without changing any shared definition. The item's DAG proof and direct proof dependencies have been updated to this argument. No shared module, definition, statement, instance, or attribute was changed. The large completed limit object and its coefficient morphism are kept irreducible locally after their projection API is established; the final record also keeps the checked pushforward and source isomorphism folded. These are local elaboration controls inside the item file. The complete single-file proof compiled in 33.7 seconds; profiling options were then removed for delivery.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_supportedSource_exists` (node `lem-sfb-diagonal-trace-supported-source-existence`). One original hole closed; zero holes added; zero holes remain in the delivery. No statements were split off, and no new module or node is added.

## No longer needed

No original import was removed: the sole original public import provides the statement interface. The proof does not need the planned general derived-pushforward composition node `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` (`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`) or tower-abelian node `det-sp-coefficient-towers-abelian` (`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`); neither is applied by this proof. This is a direct-dependency change, not a withdrawal of either module: ordinary-coherence imports retained by the reused identity helper still bring general comparison machinery into the transitive import closure. The specialized exact-image resolution argument replaces derived-composition machinery, and everything takes place in ordinary completed module sheaves rather than towers.

The planned direct dependency `lem-exc-proetale-closed-exact` is replaced by arbitrary-ring-sheaf exactness from `lem-weil-pbc-proetale-ringed-open-closed`. This removes only the item's direct dependency; closed exactness remains needed transitively elsewhere. No existing module or declaration is withdrawn, and no claim is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The statement is correct as written. The ordinary source comparison works on the empty scheme as well; the coefficient argument only uses primality to ensure the finite residue rings, and the complementary open is quasi-compact by the existing Noetherian hypothesis. The old proof plan referred to finite coefficient systems and tower exactness, although this obligation only needs ordinary completed-module pushforward. The direct exact-image argument avoids building a general derived-composition comparison. The extra diagonal-limit data in the public signature are not required for this source-existence result; the signature is preserved verbatim.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
