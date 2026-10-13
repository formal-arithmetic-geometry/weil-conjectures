# AlgebraicGeometry.openCover_map_lift_transport

Item: `Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport`; group F4.

## Reason

Elaborating the canonical adjunction comparisons repeatedly unfolded sheaf-level
constructions and exceeded the single-file limit. Combining the categorical
steps in a proved generic helper, sharing explicitly constructed comparisons,
and restricting unfolding makes the complete proof compile within that limit.
The static preflight requests this record for the local attribute and namespace
commands even though no existing public signature or definition changes.

## Old

The item contained one `sorry`, three public imports, an exposed public section,
and the original `AlgebraicGeometry.openCover_map_lift_transport` statement.
It had no private categorical helpers or local elaboration attributes.

## New

The existing theorem's signature and docstring are verbatim those of the
repository. The proof uses five proved private helpers, a proof-only import of
the new comparison-coherence statement, and two real comparison constructions
with their own modules and DAG nodes. The new statement is strictly the
canonical comparison identity; it has no transported morphism or existence
conclusion. No definition chooses arbitrary data from a new existence theorem.

The file disables optional `cleanup.letToHave` preprocessing. Scoped
`backward.isDefEq.respectTransparency` settings and a local `irreducible`
attribute protect tensor and ordinary pullback comparisons in the chart helper.
A local `instance_reducible` attribute on `Scheme.Modules.moduleBaseChange`
permits its alias to unfold in the final `with_implicit` application. The
final application uses `exact` instead of simplifying the comparison expressions. The
existing theorem alone suppresses the unused-variable linter for its original
two unused `B` lets, which are unchanged. All proof terms are kernel checked;
no unsafe reducibility override is used.

## Users

No existing signature, definition, visibility or public import changes, and no
target definition changes. The local attributes expire with their scopes. No
existing module besides the item is edited and no forced adaptation is needed.
All users continue to see the original theorem with exactly its original type.
The new public constructions and comparison statement are listed in report.md
and have matching new nodes. They require independent CODEX review.

## Status

landed 20261013T211102-L-391275 2026-10-13 (merge of deliver/F4/Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport)

Awaiting the independent second reading.

All four sandbox modules compile without errors or warnings. The original hole
is closed from one new, strictly smaller hole: this is a decomposition with net
zero holes closed. No push or delivery has been made. The first-worker dry run now allows the
second-reading section to be absent; the next worker supplies that independent
reading before delivery.
