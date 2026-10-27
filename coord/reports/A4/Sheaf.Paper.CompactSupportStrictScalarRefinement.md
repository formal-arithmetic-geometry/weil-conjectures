## What changed

Proved `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`, preserving the
specified noncartesian comparison: cartesian beta, intrinsic clopen projection,
and the named open and pullback compositors, including equality transports.

Private categorical lemmas compare the beta-inverse open-adjunction transposes
and paste the four factor squares. Forward beta follows by four inverse
cancellations. A generic coefficient-ring lemma identifies the exact alpha
factorization, retaining its associators. The complete coefficient-specific
assembly is proved in `scalar_properOpen_alpha_core`; the public theorem applies it.

Added the private proof import `Sheaf.Paper.StrictScalarPullComposition`. Moved
the existing private `scalar_jComp_named` helper before its additional use,
preserving its signature, proof, and local unfolding environment. Updated the
item's proof steps and dependency list to include pullback composition.

Local irreducibility and transparency settings prevent large derived constructions
from unfolding during conversion. Declaration-scoped removal of `catToReflQuiver`
follows the existing `StrictTowerPullbackSquarePasting` pattern. Explicit proof
type transports use this module's existing kernel-checked congruence tactic.
No instance setting is exported. No existing public signature, definition,
attribute, or public import changes.

Validation: the complete module passed remote compilation in 52.7 seconds with
profiling enabled. Removed all profiling, debug output, and temporary probe modules
before delivery; the delivery tool checks the clean module and preflight.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`
(node `lem-pur-compact-support-strict-scalar-refinement`).
Added 0 holes and split off 0 statements. No `sorry` remains in the delivered module.
Every new private helper has a complete proof. Existing dependency statements,
including `strictScalarOpenUnit`, `strictScalarPullComposition`, and
`strictScalarOpenComposition`, remain outside this delivery.

## No longer needed

None. Existing imports, dependency nodes, and the unit route are retained.
The new pullback-composition import supplies a necessary compositor equation.

## Where the brief, the DAG or earlier work was wrong

The prior proof record left the beta and compositor assembly unfinished. This
proof supplies it from the stated scalar unit and compositor equations. No
mathematical statement repair was needed. Cartesian base change is used only for
the canonical fibre-product factor; the original square can be noncartesian.

The argument also covers zero input, empty schemes, identity coefficient extension,
identity squares, and a nonempty complementary clopen component. It assumes neither
faithfulness of evaluation nor a uniform lower bound.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
