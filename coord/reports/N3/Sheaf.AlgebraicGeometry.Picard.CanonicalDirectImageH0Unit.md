## What changed

Completed the existing sandbox proof of
`AlgebraicGeometry.Scheme.Modules.canonicalDirectImageH0Unit` in
`Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit`.
The theorem's signature and all three public imports are unchanged.
Four private, fully proved helpers implement the existing node's argument:
`unit_plus`, `plus_unit_resolution`, `unit_homology_resolution`, and
`augmentation_homology`. The final proof applies naturality of the homology
factorization comparisons and cancels `toRightDerivedZero` against
`rightDerivedZeroIsoSelf` using left exactness of pushforward.

Repaired the earlier attempt's unresolved transport equality for the degree-zero
component of `mapExtendIso`. The proof now explicitly identifies the extension
index with `some 0`, transports functor maps of equality morphisms, and composes
those transports. Removed unused simp arguments and focused the resulting goals.
Helper binders are explicit, and elaboration options and the `Abelian` namespace
opening are scoped to individual declarations. No definitions, public statements,
or other modules were changed.
The existing DAG plan is followed without a route change, so no node edit is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.canonicalDirectImageH0Unit`
(node `lem-pc-canonical-direct-image-h0-unit`).
There are no remaining sorries in the item and no holes added elsewhere.
The four private helpers are proved completely; this is a proof, not a decomposition.

## No longer needed

None. No imports, nodes, or modules were pruned. The canonical single-image map,
unbounded/bounded-below derived comparison, and Grothendieck enough-injectives
instances are used. Searches from the earlier attempt and a fresh local source
search found no existing theorem for this exact canonical normalization.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt was not compilable: its `mapExtendIso` component
calculation left an equality of transport morphisms unresolved. This delivery
repairs that calculation. No mathematical error in the statement or DAG was found.
No positive-cohomology vanishing or flatness hypothesis is used; zero modules and
empty schemes are covered by the same augmentation and cancellation identities.

## Second reading by N3

1. **Comparison with the repository.** The delivered module was diffed against the
   repository version. The public imports, namespace, target declaration, and all
   existing declaration signatures are byte-for-byte unchanged; only the target
   proof and private proof helpers were added.
2. **Compilation and trust.** The module compiles with `lcompile.py`, contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and the
   target's `#print axioms` result is exactly `propext`, `Classical.choice`, and
   `Quot.sound`.
3. **Statements and split-offs.** No new public statement or split-off node was
   introduced. The four private helpers are strictly internal proof steps, and the
   existing target statement remains unchanged and mathematically sufficient.
4. **Route and pruning.** The proof follows the unit route through the derived
   direct-image comparison, bounded-below unit, injective-resolution augmentation,
   and degree-zero cancellation. All three public imports are used; no import or
   proof dependency can be pruned from this module.
5. **DAG agreement.** The existing node's statement and proof description agree
   with the implemented proof, and its unit route remains unchanged. No node file
   or change record is required.

Changed during second reading: repaired and verified the explicit `mapExtendIso`
degree-zero transport calculation in the private augmentation helper, and added
the required review record above.
