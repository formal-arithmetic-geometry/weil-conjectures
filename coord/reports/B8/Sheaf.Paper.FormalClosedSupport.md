## What changed

Restored `lean/Sheaf/Paper/FormalClosedSupport.lean` from its assigned quarantine archive.
Filled `formalClosedSupportAssertions` using the normalized formal support adjunction,
its localization triangle and Hom-complex comparison, and the proved open/closed internal
Hom formulas. Private helpers compare derived direct image followed by derived sections,
prove dualizability from the explicit covering/retract predicate, and identify derived
Hom from a single finite projective module with derived tensor by its internal dual.
Updated the existing node's proof route and dependencies; no new public theorem or node.

Made the exactness instance needed by the three derived fields of
`FormalClosedSupportAssertions` explicit using its preceding ordinary adjunction.
The theorem signature, functors, normalizations and all public imports are preserved.
The change record is `coord/changes/B8-formal-closed-support-exactness-context.md`.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupportAssertions`
(node `sk-lem-formal-closed-support`). Added zero holes. No `sorry` remains in the item,
and no new module or split-off statement is introduced. This is a proof from the stated
library interfaces; the existing `formal_closed_support_adjunction` dependency remains
unfinished in the library and is not counted as closed by this packet.

## No longer needed

Removed the private proof imports `Sheaf.Paper.FormalClosedSupportDerived` and
`Sheaf.AlgebraicGeometry.ClosedSupportStratumHom`. The original route's nodes
`det-lem-formal-closed-support-derived` and `det-lem-formal-closed-support-stratum`
are not used by this proof. The former requires an admissibility hypothesis absent
from the reviewed target; the latter uses global Hom via preadditive coyoneda instead
of the target's internal Hom followed by actual derived global sections.
Their modules are not withdrawn: other consumers may still need them.

The unit's adjunction, localization triangle and stratum argument are all retained.
No adopted source-library declaration is removed or modified.

## Where the brief, the DAG or earlier work was wrong

The assigned source was quarantined, not absent mathematics; restored its full API
and preserved its Lean attachment. The archived structure's derived fields omitted
the exactness typeclass now required by `mapDerivedCategory`. Exactness follows from
the stored ordinary adjunction, so the repair adds no hypothesis.

The original DAG's two detail interfaces do not directly compose to the target's
reviewed arbitrary-coefficient internal-Hom/global-sections statement. The direct
normalized adjunction and open/closed internal-Hom interfaces fit that statement.

`tools/downstream.py` cannot enumerate a quarantined module. The change record uses
an equivalent conservative import scan of live and quarantined sources, with live
sources preferred. No script was changed or bypassed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
