## What changed

Proved all four postponed theorems in `Sheaf.Paper.BoundedSiteAdjunctionTranspose`.
Three proved private helpers establish source naturality, target naturality, and
compatibility of the specified Hom-chain function. Every original public signature,
definition body, docstring, and public import is unchanged.

`boundedSiteRightAdjoint_plus` transports the existing specified etale boundedness
result along uniqueness of right adjoints. `boundedSiteTranspose_bijective` composes
the four canonical bijections. The counit equation follows by injectivity of this
specified transpose, its value at the counit, and the compatibility calculation.
The final theorem uses naturality of both adjunctions and the actual comparison unit.
Updated the item's DAG proof and proof dependencies to match these proofs.

Repaired the returned landing conflict (returned head `fc8485477`, old base
`061d3b229`). Started from the current shared-repository module and reapplied the
four complete theorem proofs and three proved private helpers. Checked each theorem
header against the retained proof before applying it. All current public imports,
public signatures, definition bodies, and docstrings are preserved. The four unused
private proof imports listed below are removed again. The current node was also
reloaded before applying the proof, dependency, origin, and approval-pruning edits.
No other modules require adaptation.

## Proved and sorry left

Closed the four original holes, all belonging to
`lem-pur-bounded-site-adjunction-transpose`:

- `AlgebraicGeometry.ProEtale.boundedSiteRightAdjoint_plus`.
- `AlgebraicGeometry.ProEtale.boundedSiteTranspose_bijective`.
- `AlgebraicGeometry.ProEtale.boundedSiteAdjunctionTranspose`.
- `AlgebraicGeometry.ProEtale.boundedSiteAdjunctionTranspose_naturality`.

Holes closed: four. Holes added: zero. Holes left in the delivered module: zero.
No split-off statements or decomposition.

Fresh repair validation: `lcompile.py` compiled the module in 7.5 seconds
with exit code zero and no warnings against the current compiled library.
The fresh delivery dry run also compiled the axiom probe and passed server
preflight (CODEX: node edits and returned-delivery repair). The initial dry run
failed during worktree checkout; the unchanged retry passed.
The source audit confirms all ten original public declarations are unchanged apart
from the four theorem proofs, with no prohibited token or line over 100 characters.

## No longer needed

Removed these unused proof imports:

- `WeilConjectures.AlgebraicGeometry.ProperBasic` (`pqf-lem-proper-basic`).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
  (`lem-weil-extension-by-zero-exact`).
- `Sheaf.Paper.ComparisonPullbackExact` (`lem-sf-comparison-pullback-exact`).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
  (`lem-weil-pbc-extension-by-zero-exact`).

The proof uses the existing `compactSupportSiteComparison`, so it does not separately
construct extension by zero or the proper counit mate. These former direct proof
dependencies are unnecessary here:
`pqf-lem-proper-basic`, `lem-weil-pbc-extension-by-zero-exact`,
`lem-weil-extension-by-zero-exact`, `def-sf-comparison-derived-pullback`,
`lem-cbc-proetale-extension-zero-comparison`,
`lem-weil-pbc-comparison-direct-image-canonical-mate`,
`lem-sf-comparison-pullback-exact`, and `thm-amb-etale-exceptional-adjoint`.
The supplied etale adjunction is a hypothesis, so its existence theorem is unused.
The comparison-derived-pullback definition remains a statement dependency. The
proper and open comparison results remain needed inside the canonical comparison;
this delivery does not claim their modules leave the global targets' closure.

Removed the corresponding obsolete top-level tool approvals for properness, etale
and pro-etale extension exactness, the proper mate, the open comparison, and comparison
exactness. Public reexports are retained for the existing public interface.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG expands a construction already supplied by
`lem-sf-class-compact-support-comparison`. Its precise natural isomorphism can be
reused. The existing `specifiedExceptionalEtale_boundedBelow` theorem bounds the
etale intermediate object directly, so a separate reflection-of-cohomology argument
is unnecessary. Right-adjoint uniqueness transports this bound to the supplied
adjunction. The unit's smooth-purity route and the item's statement are unchanged.

The return was a landing conflict rather than a mathematical rejection. The
current source still had the same four holes; all four are filled in this packet.
Earlier scratch logs describe superseded attempts and are not delivery evidence.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
