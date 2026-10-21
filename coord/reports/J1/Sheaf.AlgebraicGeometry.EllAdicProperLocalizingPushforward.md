## What changed

Restored `lean/Sheaf/AlgebraicGeometry/EllAdicProperLocalizingPushforward.lean`
verbatim from its quarantine archive, as required by its current rework row.
This restores the actual proper pushforward restricted to the constructible
localizing hulls, its shift and triangulated instances, its membership theorem,
and its coproduct-preservation theorem. The archive and existing DAG attachment
are preserved. Change record:
`coord/changes/J1-restore-proper-localizing-pushforward.md`.

The item compiles cleanly against the current published build (4.7 seconds alone,
5.9 seconds in the consumer check). Its proof uses the existing closure criterion,
proper bounded-constructible preservation, and proper localizing coproduct
preservation, exactly as the node describes. Searches with Lean Finder, Loogle,
the search wrapper's grep, and local `rg` found no shorter replacement of that
route. No proof imports are added or removed.

Consumer checks used temporary unmodified copies, excluded from the delivery.
`EllAdicLocalizingBrownRepresentability` compiled in 6.6 seconds and
`EllAdicLocalizingExceptionalConstructibleCohomology` in 4.3 seconds. The separate
archived `EllAdicLocalizingExceptionalBounded` has the pre-existing upstream API
errors detailed below; the ordered check stopped there, before
`EllAdicLocalizingExceptionalConstructible`.

## Proved and sorry left

The archived item has zero holes; the restored item has zero holes.
Holes closed: none (0 of 0). Holes added or split off: none.
Every existing implementation is retained:

- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightDerivedLowerStar_obj`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdicLocalizingLowerStar`.
- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_ellAdicLocalizingLowerStar`.
- `AlgebraicGeometry.ProEtale.CondensedRing.isTriangulated_ellAdicLocalizingLowerStar`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdicLocalizingLowerStar_preservesCoproducts`.

No `sorry` is left in the item or introduced anywhere by this delivery. Imported
stated dependencies retain their own proof obligations. This delivery is a
quarantine restoration, not new net proof progress.

## No longer needed

None. All archived imports and all declared proof dependencies are retained.
No module, declaration, node, or unit step is withdrawn or bypassed. The absence
of active importers does not justify withdrawing this quarantined module: four
quarantined direct consumers and its existing node still need it.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from `lean/`, and the rework archive already has a
complete zero-hole proof. The needed repair is restoration, not filling a hole.
No definition or statement repair was needed after testing the actual archive
against the current published build. The existing node and unit route agree with
the restored implementation, so no node edits or new nodes are needed.

Independent consumer rework remains: the archived
`EllAdicLocalizingExceptionalBounded.lean` fails at lines 559, 566, and 572 with
`function expected` on applications of `Mod.monoidalClosed`, and at line 660 with
unknown constant `CategoryTheory.IsCompactObject`. Those errors concern its own
private helper proofs and do not result from an interface change here. No forced
consumer adaptation is included or claimed. The consumer checks above do not
claim that all quarantined parent modules have been repaired.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
