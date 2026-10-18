## What changed

Proved `AlgebraicGeometry.Etale.exists_universalBaseChangeFailure_cyclic_datum`
in `Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum`, with its signature,
visibility, definitions and public imports unchanged. Only this Lean module is edited.

The proof starts with the declared field-failure witness, passes to its algebraic
closure, normalizes the affine base using the existing source construction, and
preserves failure using the source library's module-valued integral comparison
lemmas. Universal lower-degree base change and critical-map injectivity make the
new target nonzero. The declared prime-cyclic detection theorem supplies a prime
r dividing n. An explicit quotient-by-bottom module isomorphism identifies
ULift(ZMod r)/(r) with ULift(ZMod r). The existing higher-direct-image forgetful
comparison, the constant-sheaf comparison, and faithfulness then give the required
nonzero abelian higher direct image. Canonical pullback isomorphisms supply both
ChosenCartesianSquare witnesses and their projection equations.

Added proof-only imports of HigherDirectImageForgetComparison and
Mathlib.CategoryTheory.Sites.Adjunction. Updated the item's proof, proof_deps and
proof_origin to record the actual module-coefficient route. Added a DAG attachment
for the already-proved source integral-base equivalence; no new Lean theorem or
module is introduced. No change record is needed: no exported interface changes.

Validation: lcompile.py compiled the final pruned module cleanly in 36.9 seconds.
The import-direction check for HigherDirectImageForgetComparison passed. All Lean
lines are at most 100 characters. The delivery preflight also probes every added
constant and checks its direct holes and axiom dependencies. The theorem still
depends on existing library obligations, especially the field-failure theorem;
this delivery closes the assigned theorem's own hole rather than claiming the
whole transitive proof is sorry-free.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_universalBaseChangeFailure_cyclic_datum`
(node `sbc-lem-bc-universal-test`).

Added 0 holes; split off 0 theorems. There are no remaining sorry declarations in
the assigned module or in any Lean file added by this delivery. Existing dependency
holes are not changed or counted as new holes.

## No longer needed

Removed these proof-only imports from the assigned module:

- Mathlib.AlgebraicGeometry.Morphisms.Finite
- Mathlib.AlgebraicGeometry.AffineScheme
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
- Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
- Sheaf.AlgebraicGeometry.IntegralPushforwardBaseChangeArrow
- Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
- Sheaf.AlgebraicGeometry.IntegralSurjectiveTargetBaseChange
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap

The last import is redundant because CurveTestDatum exports the same critical-map
API. Its injectivity argument is retained, via the directly stated fixed-base
lemma `lem-sbc-fixed-base-critical-map`. The other Mathlib modules are also
available through the retained source import; no geometric permanence argument
is removed.

The following planned dependencies are no longer direct proof dependencies:

- `lem-sbc-coefficient-higher-direct-image-zero`: the witness already uses module
  coefficients; the final conversion uses the more direct
  `lem-sbc-higher-direct-image-forget-comparison`. Restriction of scalars is not
  needed to enter or leave the prime-cyclic detector.
- `lem-sbc-integral-pushforward-base-change-arrow`: its abelian statement would
  require extra coefficient conversions before and after normalization. The
  existing source integral-base module equivalence supplies exactly the required
  implication. The new attachment records that source declaration.
- `sbc-lem-bc-integral-surjective`: use the existing fixed-base module lemma
  `lem-sbc-module-bc-integral-surjective`, directly accepting the pasted square,
  rather than building an additional pullback square for the recorded wrapper.
  This preserves the same integral-surjective step of the unit's route.
- `sbc-lem-bc-injectivity`: use its existing fixed-base first-clause theorem,
  recorded as `lem-sbc-fixed-base-critical-map`, rather than the three-clause
  universal wrapper. The injectivity step itself stays in the proof.
- `sbc-def-base-change-map`: no separate theorem or comparison from
  BaseChangeMapAbelianAndSets is needed; the canonical module base-change map
  is already the map supplied by the retained source definitions.

Removed only the obsolete `sbc-lem-bc-injectivity` entry from the item's existing
`tool_uses`; the other approved entries remain in order. No module is withdrawn.
Some removed direct imports can remain transitively reachable through retained
source modules; this report does not claim they all leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The source already contains the integral-base isomorphism equivalence needed to
preserve module-valued failure. There was no DAG attachment for that declaration,
only a source-place mention in the abelian arrow-comparison node. The new node
attaches the exact existing declaration instead of introducing another obligation.

The item docstring's coefficient-comparison route is longer than necessary with
the available prime-cyclic detector and HigherDirectImageForgetComparison. The
statement is unchanged; the revised DAG spells out the comparisons actually used.

Read the current blueprint node and unit, the recorded DAG plan, and Stacks
etale-cohomology.tex, lemma-base-change-does-not-hold (0F08) and
lemma-base-change-q-integral-bottom (0F05). The construction retains the field,
algebraic-closure, normalization and cyclic-coefficient reductions of the unit.
Normalization before prime detection follows the already-reviewed six-step DAG
route and the existing source proof; it avoids asserting an arbitrary-ring
cyclic decomposition. The exact cyclic abelian conclusion remains unchanged.

Checked q=1 explicitly through the cast identity: q-1 is degree zero, with no
negative-degree hypothesis used. For n=1 the module coefficient category is zero,
so the failure hypothesis has no witness; no division or primality assumption on
n is introduced. The final quotient comparison also needs no extra prime-field
instance. Empty schemes are allowed by all comparison lemmas. Normalization
produces an integral nonempty base from the field point, as required.

## New nodes

`lem-sbc-module-integral-base-change-iso` attaches the existing theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`
in WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange.
It states the integral replacement equivalence for module-valued degreewise
base-change maps, for every integer degree and arbitrary coefficient ring.
Its proof is already present in the source library: compare the pushed inner
arrow to the pasted arrow, preserve invertibility in one direction, and use exact
conservative integral pushforward in the other. Mathlib searches and the blueprint
search were run; the latter found the related abelian blueprint statement
sbc-lem-bc-integral-base, but no duplicate of this coefficient-general equivalence.
This adds no Lean file, no choice of data, and no sorry.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
