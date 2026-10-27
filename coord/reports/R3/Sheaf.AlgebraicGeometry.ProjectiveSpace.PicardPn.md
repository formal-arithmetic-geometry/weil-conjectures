## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.picard_pn` in the assigned module, with its
statement unchanged. The existing source library already implements the unit's standard
Cech and Laurent-monomial computation. The proof composes its polynomial and dual
isomorphisms with a private linear comparison from module-derived cohomology to source H.
Naturality under scalar endomorphisms proves linearity. Vanishing is transported through
this equivalence and `ModuleCat.isZero_iff_subsingleton`.

The dimension-zero scheme isomorphism is proved from its sole standard chart and empty
coordinate affine space. All twists are trivialized by their chart free generator.
The canonical sheaf follows from the existing `exteriorSheafIsoExteriorPower` and
`canonicalModuleIsoTwist`, including dimension zero. The structure-sheaf clauses follow
from O(0), the unique degree-zero monomial, and middle/top vanishing.

Added private proof imports of ProjectiveSpace.Canonical, Cohomology.ProjectiveSpaceTwist,
ModuleCohomologySourceComparison, ModuleCohomologyScalarEndomorphism, and
Sheaf.AlgebraicGeometry.ExteriorSheafComparison. Replaced the proof-only Differentials
import with Canonical. All public imports, declarations and target types are unchanged.
Updated the item's DAG proof and dependencies to describe this assembly. No other module
or definition is changed. Source read: Stacks coherent.tex, lemma-cohomology-projective-space-
over-ring (01XT), its exponent contraction and equation-identify; current blueprint
sk-thm-picard-perfect/det-thm-picard-pn and its proof, and the canonical-sheaf lemma.

Validation: final module compiles cleanly in 11.3 seconds; an additional axiom probe
compiled in 10.2 seconds and reports only propext, Classical.choice, Quot.sound for
picard_pn. This is a complete proof, not merely a reduction to sorry-bearing statements.
The formula retains n=0 separately and the positive-dimension hypotheses on top cohomology.
At m=-n the top group vanishes; at m=-n-1 its dual polynomial degree is zero. The canonical
isomorphism applies for all n, and no algebraic-closure hypothesis is introduced.

## Proved and sorry left

Closed the original one hole: `AlgebraicGeometry.ProjectiveSpace.picard_pn`
(node `sk-thm-picard-pn`). Proved 1 of 1 original sorries; added 0 holes; split off 0.
No sorry remains in the delivered module. All five private helper theorems are proved.
The final axiom audit establishes that the assembled theorem has no transitive sorry.

## No longer needed

Removed direct private imports:
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`;
- `WeilConjectures.AlgebraicGeometry.AlternatingCechComputes`;
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials` (Canonical supplies
  the actual canonical-bundle isomorphism).

The item's proof no longer directly needs nodes `lem-pc-cech-computes` or
`lem-pc-alternating-cech-computes`; deleted their obsolete top-level tool_uses approvals
in the item copy. The source's already proved twist-cohomology API packages its Cech route.
These generic source declarations are preserved, and this delivery withdraws no module.
The unit realization explicitly includes `lem-pc-twist-cech-monomial-decomposition` and
`lem-pc-monomial-cech-complex-homology`, so their private imports and DAG dependencies stay.
They are retained as required unit-route imports although this wrapper uses the source's
proved computation. Neither is claimed pruned. No whole-library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The canonical node's current Lean attachment names only
`isFiniteLocallyFreeOfRank_relativeDifferentials` in ProjectiveSpace.Differentials.
That declaration supplies local freeness, not the canonical isomorphism. The full
canonical statement is already proved by `canonicalModuleIsoTwist` in
ProjectiveSpace.Canonical, as the current blueprint lists. We use that declaration
without weakening or changing the node's mathematical statement.

The earlier plan's assertion that the two exterior sheaves are exactly the same needs
an explicit comparison: their restriction maps are different constructions. The already
proved ExteriorSheafComparison module supplies the precise canonical isomorphism.
Similarly, source H and RingedSpace.moduleCohomology are different constructions; the
natural additive comparison alone is not a field-linear isomorphism until scalar
naturality is checked. The private linear comparison supplies that check.

The module imports the two explicitly realized unit-route modules in compliance with
the unit restriction, rather than claiming their now redundant direct use has pruned them.
The static preflight classifies the added open command as an interface command and
requires a change record. `coord/changes/R3-picard-pn-proof-scope.md` records its exact
old/new scope and zero consumers. No statement repairs or new nodes were required.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
