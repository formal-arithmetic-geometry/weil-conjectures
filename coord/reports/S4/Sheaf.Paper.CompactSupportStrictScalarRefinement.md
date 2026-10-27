## What changed

Completed `WeilConjectures.PurStrictScalar.scalar_compactification_composition` from the
existing `scalar_properOpen_gamma` and the scalar compatibility equations for the
specified open and direct-image compositors. A proved private categorical pasting
lemma supplies the assembly: naturality moves the outer proper comparison, the two
compositor equations handle the outer normalization maps, and the central mate
square handles gamma. The proof also treats the equality transports `c.i_q` and
`c.p_g`; the comparison maps are exactly the existing `compositionD` and `comparison`.

Added `StrictScalarOpenComposition`, `StrictScalarPullComposition`, and
`StrictScalarProperComposition`. The direct-image compositor equation is proved from
the pullback compositor equation by the geometric adjunctions, with the ordered
composite counit verified explicitly. The other two compositor equations remain
named smaller statements. Existing public signatures, definitions, attributes and
public imports are unchanged. New imports in the item are private proof imports.
Updated the item's proof record and supplied nodes for the three new statements.
The scoped local proof commands are recorded in
`coord/changes/S4-strict-scalar-composition-proof-scope.md`.
The compositor inputs use the item's existing kernel-checked structural type
transport; this avoids expensive definitional comparison of derived-functor
instance presentations. Large scalar maps stay locally irreducible only within
the new composition proof's section. No public reducibility status changes.

Validation: the complete item module compiled through `lcompile.py` in 35.3 seconds,
with no warnings or errors. The proved proper-composition module also compiled
independently in 6.2 seconds. Both new statement modules compiled. All temporary
profiling options and diagnostic modules have been removed.

## Proved and sorry left

One of the item's two original holes is closed by decomposition:
`WeilConjectures.PurStrictScalar.scalar_compactification_composition`
(node `lem-pur-compact-support-strict-scalar-refinement`). Its proof uses the existing
central mate equation and two separate geometric compositor compatibilities.

The new theorem
`WeilConjectures.PurStrictScalar.strictScalarProperComposition`
(node `lem-pur-strict-scalar-proper-composition`) is proved by mate pasting from the
pullback compatibility. No hole is left in its module or any private helper.

Exactly three theorem holes remain in this packet:

- Existing, untouched: `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`
  (node `lem-pur-compact-support-strict-scalar-refinement`).
- Added: `WeilConjectures.PurStrictScalar.strictScalarPullComposition`
  (node `lem-pur-strict-scalar-pull-composition`).
- Added: `WeilConjectures.PurStrictScalar.strictScalarOpenComposition`
  (node `lem-pur-strict-scalar-open-composition`).

Thus one original hole is closed and two are added: a decomposition, not a net
hole reduction. The new pullback and open equations are independent ingredients
for arbitrary composable scheme maps or open immersions; neither restates the
compactification comparison. They have no compactification, native reduction
model, constructibility, inverse-limit or refinement hypotheses. Empty schemes,
zero complexes, identity maps and identity coefficient extensions retain the
same unit/counit and open-summand equations. All data definitions remain unchanged.

## No longer needed

None. No existing import, module, node or unit route is withdrawn. In particular the
existing strict proper/open calculus and its normalized central gamma are retained.
The new proper-composition proof still uses the pullback-composition statement.

## Where the brief, the DAG or earlier work was wrong

The original Step 9 describes proper/open mate pasting, but its Lean theorem still
needed explicit compatibility with both prescribed geometric compositors. This
packet supplies the categorical assembly and exposes those concrete compatibility
inputs as separate smaller statements. `OrdinaryOpenScalarComposition` composes
coefficient extensions at a fixed open immersion, so it does not supply the needed
equation for two composable open immersions.

The rework row names an old quarantine location. The assigned module is present in
the current shared source; this packet starts with that current module and preserves
its Lean attachment and dependencies. It does not withdraw or delete any archive.

## New nodes

`lem-pur-strict-scalar-pull-composition`, in
`Sheaf.Paper.StrictScalarPullComposition`, states compatibility of the inverse
scalar/pullback comparison with `gComp`. Its source is the parent's Steps 3--4 and
Stacks' derived pullback/direct-image composition and adjunction normalization.
The proof in words derives the identity-on-sections restriction square and takes
its conjugate with the specified whole-complex units.

`lem-pur-strict-scalar-open-composition`, in
`Sheaf.Paper.StrictScalarOpenComposition`, states compatibility of `openTensor`
with `jComp`. Its source is Tag 0E8I and the open composition normalization in
0F7D. Its proof follows an elementary tensor through the same composite open
summand, then localizes the equality of maps of strict complexes.

`lem-pur-strict-scalar-proper-composition`, in
`Sheaf.Paper.StrictScalarProperComposition`, proves the `proper`/`rComp` equation
from the pullback equation. Its source is Tag 07A6 and the composition-adjunction
argument of `lemma-derived-pushforward-composition`. Its Lean proof computes the
composite counit and takes mates of the pullback cube.

LeanSearch and LeanFinder returned ordinary coefficient-composition maps and generic
mate identities. Loogle found the mate calculus used here. Searches of Mathlib,
`lean/Sheaf` and `lean/WeilConjectures` found no equation for these concrete strict
geometric compositors; the coefficient cocycle at a fixed map has different inputs.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
