## What changed

Restored `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent` from the
quarantine path recorded in `coord/rework.tsv`. Removed `derivedPullback` from
the local irreducibility attribute command: the current source defines it as
globally irreducible, and the repeated local attribute is rejected by Lean.
This is the only change from the archived Lean text. The complete proof of
`AlgebraicGeometry.perfectOverlapTailProjectionComponent` compiles unchanged
after that repair (16.4 seconds, no warnings).

The proof uses the existing restricted-composition and nested-square equations,
`compositionTo_prism`, the two stage-object component equations, and
`perfectOverlapProjectionCompositeAbstract`. Naturality of the inclusion and
transport comparisons combines them, and Boolean elimination supplies the two
components. The node's existing proof plan and dependencies already describe
this argument and are preserved. Its Lean attachment remains intact. The unit
`sk-thm-picard-semicon` and its realized route are unchanged.

The quarantined direct consumer
`Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent` was read;
its application of the restored theorem has exactly the same signature and
conclusion. No consumer is adapted. The change record is
`coord/changes/N2-perfect-overlap-tail-projection-restoration.md`.

## Proved and sorry left

This is a zero-hole restoration and compilation repair. The archived and
restored module each contain zero `sorry`s. The complete theorem
`AlgebraicGeometry.perfectOverlapTailProjectionComponent`, attached to
`lem-pc-perfect-overlap-tail-projection-component`, is retained and compiles.
Holes closed: zero. Holes added: zero. Holes remaining: zero. No statement is
split off and no new declaration is introduced.

## No longer needed

None. No imports, nodes, modules or declared dependencies are pruned. Only the
redundant local irreducibility attribute entry for `derivedPullback` is removed;
its global irreducibility supplies the same behavior.

Loogle found the usual naturality API; Lean Finder found scheme restriction and
pullback projection equations, but no replacement for this fixed derived
comparison identity. Searches of both project roots locate the existing prism
and stage-object component APIs used by the archived proof. There is no reason
to replace that complete argument or its declared dependencies.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined, not withdrawn.
Its rework row was read before restoring the archive. The original compile
fails at the local attribute command with: "failed to set [local irreducible],
derivedPullback is currently [irreducible]". Removing the redundant entry fixes
the failure without changing any mathematical construction or statement. The
existing DAG plan remains accurate. No archive is deleted and no dependency is
removed. There is no new statement to test or dispute.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
