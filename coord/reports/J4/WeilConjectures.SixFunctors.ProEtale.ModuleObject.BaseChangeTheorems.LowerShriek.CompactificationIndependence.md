## What changed

Proved all three existing isomorphism theorems in the assigned module. Existing signatures,
attributes, public imports and all non-theorem bodies are preserved. Added proved private
helpers and three private proof imports.

For the restriction comparison, cartesian abelian-sheaf base change makes the open counit
invertible on pulled-back extensions by zero. Forgetting module structure reflects this
property; scalar transport, exact derivation and fully faithful restriction transfer it to
bounded constructible complexes. The restriction comparison is then a composite of
isomorphisms, using the invertible open-adjunction unit and triangle comparison.

For the pushforward comparisons, apply the existing proper/open interchange theorem with
identity upper vertical map. Its mate factors as the proper-map adjunction unit followed by
isomorphisms, since the identity-map counit is invertible. Cancellation and the canonical
identity-pushforward isomorphism show that the unit is invertible on extensions by zero.
Compose it with the inverse restriction comparison. This proves the finite-extension and
algebraic-closure coefficient cases separately using their existing interchange theorems.

The prerequisite cluster was initially quarantined. It has since been restored in the
shared library; all auxiliary sandbox copies and experimental diagnostics are omitted.
The delivery changes only the assigned module and its report/change record.
The change record is `coord/changes/J4-compactification-independence-restoration.md`.

## Proved and sorry left

Closed all three assigned holes in namespace `AlgebraicGeometry.ProEtale.CondensedRing`:

- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`.
- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`.
- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl`.

Zero holes remain in the delivered module; zero holes are added or split off. These are
proofs from existing library declarations, including proper base change; they do not claim
that every transitive imported theorem is already axiom-free.

## No longer needed

No mathematical node, module or source declaration is withdrawn. No existing public import
is removed. Two trial private imports, `Derived.OpenImmersionEssImage` and
`ModuleObject.OpenClosed`, were removed because the retained interchange import exposes them.
The retained private imports are bounded constructible pullback, proper/open interchange,
and abelian extension-by-zero base change. All restored prerequisite modules are supplied
by the current shared library and are omitted from the delivery.

## Where the brief, the DAG or earlier work was wrong

The assigned source was quarantined, not withdrawn, and is now restored in the shared
library. No DAG node has a Lean attachment naming this module. Related compactification
and general-base-change nodes have different current Lean attachments or coefficient and
category statements; this delivery does not overwrite those attachments. No new public
statement or postponed proof is introduced, so no new node is needed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
