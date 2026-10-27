## What changed

Completed the assembly proof of
`WeilConjectures.ZlOpenComplement.restrictionIdentities` without changing its
statement, public imports, or definitions. Added private proof helpers for the
actual base-changed image complement, empty pullback, factorization of arbitrary
field-valued points, empty-site module and derived vanishing, stage localization,
strict reduction, scalar compatibility, and common-stage zero preservation.
Added private imports of `Mathlib.AlgebraicGeometry.PullbackCarrier`, the new
integral vanishing lemma, `IntegralStratumChartRestrictionsFunctorial`, and
the source-library finite-type dimension and Noetherianity results. No existing
declaration signature changes and no consumer adaptations are needed.

The remaining integral construction argument is isolated as one strictly
smaller step: integral open-support vanishing across an empty pullback. It has
no rational, common-stage, scalar-coherence, normalization, or geometric-point
conclusions. Ambient integral pullback zero preservation at the geometric point
follows from the existing integral-stratum functoriality theorem: both schemes
are Noetherian of finite dimension. The unit's completed open-base-change route
remains in the new integral vanishing lemma.

## Proved and sorry left

Closed the existing hole
`WeilConjectures.ZlOpenComplement.restrictionIdentities`, reducing it to the one
new statement listed below. This is a decomposition, not an independent
axiom-free proof. The item's module has zero remaining holes.

The two finite-type helpers `WeilConjectures.ZlOpenComplement.closedDomainFT`
and `WeilConjectures.ZlOpenComplement.closedDomainQC` were proved in the shared
source during this session; their proofs agree with this packet, so no credit
for those holes is claimed.

Added one hole, a public theorem with its source and full proof in words:

- `WeilConjectures.integralOpenEmptyPullbackVanishing`
  (`lem-zl-integral-open-empty-pullback-vanishing`).

The final delivery compile/preflight checks both modules. Local irreducibility
for the ambient integral pullback and the private comparison record prevents
expensive unfolding during final assembly. No construction or public API changes. There are no
holes in definitions or private helpers.

## No longer needed

No existing module is withdrawn, and no public import is removed: each belongs
to the unchanged statement/definition interface. All added proof imports are used.

The parent proof no longer separately needs the three scalar compatibility
theorems `lem-weil-compact-support-normalized-scalar-isomorphisms`,
`lem-weil-compact-support-normalized-scalar-descent`, and
`lem-pur-integral-operations-scalar-extension`: its displayed equations have
zero target and follow by uniqueness. Removed these three obsolete top-level
`tool_uses` entries. Their existing definitions and public interfaces remain
used and are preserved. No assertion is made that these modules are globally
unreachable.

The direct proof dependencies `def-weil-extension-by-zero-presheaf`,
`def-weil-presheaf-modules-sheafification`, and
`lem-cbc-completed-extension-zero-comparison` move into the integral
empty-pullback lemma's proof; they are still needed there, not globally pruned.
The coefficient-extension definition remains a statement dependency and is
not an extra proof step. The Mathlib pullback-range formula replaces the
planned separate affine image computation, and Mathlib's surjective closed
immersion onto a reduced scheme replaces a separate gluing argument for points.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The integral pullback does not expose a
generic zero-preservation instance. A later search found that the existing
integral-stratum functoriality theorem supplies additivity under the hypotheses
available at the geometric point, avoiding a new zero-preservation statement.
Rational pullback additivity is available from its existing unique specification. For common
pullback the recorded object formula on a bottom-stage zero object suffices;
no new common-stage additivity assumption is added.

Checked the new statement on empty schemes, zero inputs, nonreduced closed
complements, and arbitrary (including non-closed) field-valued points. The
factorization proof only uses the reduced source field spectrum and does not
assume a reduced complement. The new integral vanishing lemma allows an
arbitrary map into the ambient scheme with empty pullback, so the actual closed
complement is a valid specialization.

## New nodes

`lem-zl-integral-open-empty-pullback-vanishing` is the integral-object step of
the original complementary restriction argument, stated in
`Sheaf.Paper.IntegralOpenEmptyPullbackVanishing`. Its node records the specified
open reduction, integral/completed comparison, completed open exchange, and
empty-site argument, rather than repackaging the parent theorem.

Updated the parent node's proof, proof dependencies and proof origin to match
the Lean assembly. No existing definition or statement was changed, so no
change record is required.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
