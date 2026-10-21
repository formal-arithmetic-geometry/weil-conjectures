## What changed

Completed the duplicate retirement listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`.
The adopted source already proves
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_presheaf_class_cover`
with the identical conclusion and all the same hypotheses except the unused `hK`.

Withdraw the duplicate through `deleted.txt`. In its sole direct consumer,
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent`, replace the private
proof import by the source module and omit `hK` in the call. Keep the consumer's
public signature and docstring unchanged; reference `hK` locally to satisfy the
unused-variable linter. Reattach the existing node
`lem-sbc-higher-direct-image-limit-presheaf-class-cover` to the source theorem and
record that theorem's signature verbatim. The source theorem and all other source
files are untouched.

The change record is
`coord/changes/R5-retire-higher-direct-image-limit-presheaf-class-descent.md`.

## Proved and sorry left

This is a duplicate repair, with zero holes initially, zero holes closed and zero
holes added. The retired theorem
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_presheaf_class_cover`
already had a complete proof. Its source replacement also has no direct sorry.
The adapted consumer
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_rep` has no direct
sorry. No split-off theorem, new declaration, or new node is introduced.
Existing transitive proof dependencies are retained; this packet does not claim
their holes as proved.

The replacement and old signatures were compared binder by binder. The only
extra old hypothesis is `hK`, which its own proof did not use. The same affine
cover proof works for empty objects, degree zero, and singleton index systems;
the source replacement preserves those cases. The adapted consumer was compiled
with lcompile.py; the delivery performs the final compile and axiom probes.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`.
Removed its private import from
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent` and replaced it with
`WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`.
The now-withdrawn module's private affine-representative import is retained through
the source replacement; the affine representative node and its dependencies are
still needed. No mathematical node is pruned: the same local class-cover node is
realized by the adopted source declaration. No upstream declaration is removed.

The sole semantic parent is
`sbc-lem-higher-direct-image-limit-class-descent`; its dependency edge is preserved
and the corresponding Lean consumer is migrated in this delivery. No quarantined
Lean consumer was found. `sk-lem-failure-field` has no realized attachment requiring
the retired duplicate. The affine-cover argument and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief names an item whose current Lean proof is already
complete. The current retirement inventory identifies the actual duplicate repair.
The inventory marks the signatures DIFFERENT because the source omits `hK`; this
is a harmless strengthening, rather than a missing compatibility condition: local
lifting uses `hη` and naturality of `η`, not the equation for `K.map`.

LeanFinder and Loogle searches via msearch.py returned generic cohomology and sieve
APIs. Grep across the library found the exact stronger adopted source theorem.
The existing DAG proof plan agrees with that theorem's proof, so no new geometric
lemma or further decomposition is necessary.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
