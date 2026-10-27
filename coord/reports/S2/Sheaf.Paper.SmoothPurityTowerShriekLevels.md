## What changed

The unchanged theorem `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_shriek_levels`
now obtains the actual b,o,x from the existing normalized strict comparison
realization and assembles Laws. Its proof establishes boundedness using the
canonical D+/unbounded pushforward comparison, joint conservativity using the
existing semilinear calculus, and projection invertibility from a finite-level
criterion and the specified projection evaluation identity, followed by
conservativity. Localization uses a separate residual transport of the strict
short exact complex sequence. The third residual supplies the exchange field
from the normalized finite and tower comparison words.

The declarations R through Laws moved verbatim to
`Sheaf.Paper.SmoothPurityTowerShriekData`, publicly reexported by the item.
The comparison data module now publicly imports that shared tower data module,
so it can be used by the item's proof without an import cycle. The declaration
names, universes, signatures, bodies and instance attributes are unchanged.
A source comparison with comments removed verified exact equality of the moved
interface code. All 403 current downstream modules are listed in
`coord/changes/S2-tower-shriek-interface-extraction.md`; no consumer adaptation
is needed. F4's current comparison realization and all its proof dependencies are preserved.
The adapted comparison data module changes only its interface import. Current
consumers retain all interface declarations; the sole external executable user of the upper
theorem imports the item explicitly. `TowerP1ProperCtf` mentions it only in a
docstring.

## Proved and sorry left

One original hole is removed from `tower_shriek_levels`, with a complete Lean
assembly from existing declarations and three strictly smaller residual steps.
This is a decomposition, not a net hole reduction or an axiom-free proof of
the target closure.

The delivery adds exactly three holes:

- `AlgebraicGeometry.ProEtale.SpTowerShriek.finite_level_projection_criterion`,
  node `lem-sp-finite-level-projection-criterion`, in
  `Sheaf.Paper.SmoothPurityFiniteLevelProjectionCriterion`: one positive
  coefficient level, before joint conservativity on towers.
- `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_localization_realization`,
  node `lem-sp-tower-localization-realization`, in
  `Sheaf.Paper.SmoothPurityTowerLocalization`: the identification and localization
  of the existing ordinary strict-system counit-unit short exact sequence.

- `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_exchange_laws`, node
  `lem-sp-tower-exchange-realization`, in `Sheaf.Paper.SmoothPurityTowerExchange`:
  the exchange field from the normalized finite and tower comparison words.

F4 proved
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictCompactificationComparisonRealization`
on current main. That proved module is preserved verbatim and has zero holes.
The adapted comparison data module also has zero holes. No hole is left in
the item or the new data module; no private declaration or definition contains
sorry. All three new holes have standalone public theorem statements, sources,
complete natural-language arguments, and DAG nodes. Their zero-input and
empty-scheme cases use the same comparisons and cancellation; all levels are
positive and no transition compatibility on etale origins is imposed.

## No longer needed

The data-only module removes the old item's proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`,
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`, and
`Sheaf.Paper.SmoothPurityTowerInjectiveComponents`. None is used by a data
construction. The original public imports are retained through the shared
module. These are import cleanups, not claims that the corresponding mathematics
is globally unused: the normalized comparison realization still uses the tower
injective-components route, and the localization residual still needs the strict
open-closed sequence and the SES triangle. No module is withdrawn or globally
pruned.

The item no longer separately re-proves the cone-conservativity argument:
`Base.calculus.detects` supplies exactly its unbounded assertion. Accordingly
`lem-kun-distinguished-cone-zero` is no longer a direct proof dependency of this
item. The direct proof dependencies for ordinary open extension, SES triangles,
exact-functor derivation, finite projection and Tor reflection move below the
normalized realization or the three residual steps, as recorded by the updated
nodes. They remain needed there. No unit route is changed. The read-only source
`literature/stacks-project/proetale.tex` was checked at
`lemma-closed-immersion-complement-retrocompact-exact` and
`lemma-ses-associated-to-open`: quasi-compactness of the complementary open gives
exact closed pushforward and the canonical counit-unit short exact sequence,
with no qcqs hypothesis on T.

## Where the brief, the DAG or earlier work was wrong

Returned head `6f1f7ab3b2a` conflicted with F4's landed `b59b636ad25`.
The current 133-line comparison realization replaces the stale 753-line sandbox
copy and keeps F4's completed proof verbatim. Its extracted comparison data module
now carries the dependency on the item, so this repair redirects that module's
one public import to the shared tower data module.

The stated comparison dependency originally publicly imported the item containing
its interfaces. The suggested proof
import was therefore cyclic: import_direction.py reported that the dependency
already reaches the item. The interface extraction resolves that cycle without
changing any mathematical data. The normalized realization already supplies
Base.calculus.detects and the D+ compatibility, so the planned separate cone
proof and direct injective comparison are unnecessary at the assembly level.

The new residuals name genuine remaining steps: finite projection
invertibility in the correct intrinsic/fixed-scalar coordinates, and the
identification of the semilinear short exact sequence with the existing
Geometry/Open coordinate choices. None repeats the full item or introduces
an existence hypothesis equivalent to it. The exchange field remains a named residual with its complete argument: the
attempted finite cancellation triggers expensive definitional equality of the
coefficient sheafification endpoints. Its
proof in words uses the existing finite base-change theorem and needs no
quotient-coefficient transport.

The unit record has no binding realized nodes, and the blueprint operations
proof (1), (3), (2) remains the route. New generic tools from other units are
used as black boxes: semilinear derived calculus for conservativity and the
existing finite compact-support exchange transport theorem for witness
normalization. The maintainer may record the corresponding tool approvals;
this delivery adds none itself.

## New nodes

`def-sp-tower-shriek-data` attaches the existing interface declarations at their
new shared module, with all names and bodies preserved. It introduces no new
mathematical construction and no hole.

`lem-sp-finite-level-projection-criterion` records finite projection
invertibility at one n from the normalized finite comparison and the existing
finite coefficient/Tor comparison theorems. Its full Lean statement is in its
own module and its proof in words is in both its docstring and node.

`lem-sp-tower-localization-realization` records the coordinate transport of the
strict semilinear complex sequence, its SES triangle and the evaluated
boundary. Its full Lean statement is in its own module with its proof in words.

`lem-sp-tower-exchange-realization` records the exchange field from retained
origins and the normalized finite and tower comparison words. It includes finite
witness transport, comparison cancellation, naturality and tower detection.
It does not assert the other fields of Laws or existence of the full calculus.

Change record: `coord/changes/S2-tower-shriek-interface-extraction.md`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
