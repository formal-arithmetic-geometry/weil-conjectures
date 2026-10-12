## What changed

Kept the existing signature and docstring of `Algebra.subsingleton_h1Cotangent_of_charP`
byte for byte. Its proof derives primality from positive field characteristic, then proves
vanishing for each finitely generated intermediate field using Mathlib's
`IntermediateField.essFiniteType_iff`, `Algebra.FormallySmooth.of_perfectField`, and
`Algebra.FormallySmooth.subsingleton_h1Cotangent`. It applies the new finite-subfield
reduction from `Sheaf.RingTheory.H1CotangentFiniteSubfields` to conclude.
Only proof imports were replaced. The target node now records this actual route.

## Proved and sorry left

Hole closed: `Algebra.subsingleton_h1Cotangent_of_charP`
(`lem-weil-pbc-field-char-p-h1-cotangent-vanishing`). There are no sorries left in its module.
Hole added: `Algebra.subsingleton_h1Cotangent_of_finite_subfields`
(`lem-weil-pbc-h1-cotangent-finite-subfields`), in its own new module, with the full
finite-support proof and source in its docstring. This is a decomposition, not an
axiom-free proof: one original hole closed, one new hole added; local net zero.
The finite-subextension vanishing is fully proved using Mathlib, without a new hole.
The first worker's proposed `Algebra.isSeparableExtension_zmod` and
`Algebra.subsingleton_h1Cotangent_of_isSeparableExtension` were removed before delivery,
together with their two proposed nodes and `CharPFieldSeparable.lean`.

Both delivered files compile without warnings. A scratch-copy `#print axioms` check
of both declarations shows only `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx` from the listed finite-subfield hole.

## No longer needed

Removed proof imports:
- `Sheaf.FieldTheory.MakeSeparable`
- `Sheaf.FieldTheory.SeparableExtension`
- `Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra`

Old proof-dependency nodes no longer used by this route:
- `lem-weil-pbc-make-separable`
- `def-weil-pbc-separable-field-extension`
- `def-weil-pbc-finite-purely-inseparable-extension`
- `def-weil-pbc-transcendence-basis`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra`
- `lem-weil-pbc-h1-cotangent-localization`
- `def-weil-pbc-module-localization`

`def-weil-pbc-smooth-ring-map` and `def-weil-pbc-mv-polynomial-ring` remain used by the
new finite-support node. All ten old direct proof dependencies are replaced in the
item's node by the finite-subfield reduction. The two existing public Mathlib imports
remain unchanged. Added proof imports are plain imports of `Mathlib.Algebra.Field.ZMod`,
`Mathlib.RingTheory.Smooth.Field`, and the finite-subfield module. Removed a redundant
explicit import of `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` after compilation.
These are removals from this proof; whole-library pruning and closure net figures are
for the maintainer's pinned-baseline sorry ledger, not inferred from this delivery.

## Where the brief, the DAG or earlier work was wrong

The first proposal compiled with long-line and letI warnings. Its two new sorry theorems
had no source/proof docstrings or blueprint markers; their nodes had empty proof plans,
missing searches, and informal text instead of Lean signatures. The existing target node
was not updated. The characteristic-p separable-cotangent statement repackaged almost the
whole target after the universally true separability claim. That proposal was replaced
by the real finite-subextension/finite-support reduction. Mathlib already discharges the
finite-subextension part directly; the old make-separable/smooth-fraction-field route
was unnecessary below the unit level.

## New nodes

`lem-weil-pbc-h1-cotangent-finite-subfields` states the characteristic-independent
finite-support reduction: if first cotangent homology vanishes for every finitely
generated intermediate field of a field extension, it vanishes for the extension.
Source: [Stacks Tag 07BQ](https://stacks.math.columbia.edu/tag/07BQ), used in
[Tag 0320 (3)](https://stacks.math.columbia.edu/tag/0320). The source proof was also
read in `/home/ubuntu/c1-stacks-review/algebra.tex` at the corresponding labels.
It isolates only the last step of the original proof. No changes to an existing
statement or definition, and no change records or forced adaptations.

## Second reading by H1

1. Compared the target module to the repository with diff and the delivery declaration
parser: existing signature, visibility, public imports, and docstring unchanged;
only its proof and proof imports changed. No existing data definition changed.
2. Compiled both modules in dependency order through lcompile.py without errors or
warnings, and checked both declarations with #print axioms in a scratch copy.
Only the standard three axioms and the listed lower sorryAx remain. No forbidden
axiom/unsafe/opaque/extern/implemented_by, or any sorry inside a definition.
3. Checked the new finite-support lemma against the source and small cases: the bottom
field handles empty support; for a finitely generated ambient field the hypothesis
includes the top field; for arbitrary unions every polynomial still has finite support.
Its hypothesis is essential, and it makes no perfectness or separability assumption.
Searched Mathlib with leanfinder, loogle, and grep, and searched local Sheaf/upstream
sources; no matching finite-subfield reduction exists. Leansearch was attempted but
returned Internal Server Error, recorded as unavailable without a verdict.
4. The proof now follows the shorter Mathlib route for finitely generated subfields,
then retains the finite-support step. Inspected sk-thm-p1.json realized: this node is
below the unit level, none of its removed dependencies realizes a unit statement or
step, and the projective-line/curve/PBC route is preserved. The pruning list covers
every old proof dependency. Public imports are unchanged; added proof-only imports
are plain, and the new module exports only the imports needed in its statement.
5. Updated the original node's proof, proof_deps and proof_origin, and supplied a new
node with the exact Lean signature, complete proof steps, source, dependency union,
search records, creation provenance and unchanged chapter/unit ancestry. Verdict:
the repaired delivery is a sound decomposition with one identified lower obligation.

Second reading changed: replaced the two-hole separability proposal by Mathlib
finite-subfield vanishing plus one finite-support hole; repaired nodes and reporting,
removed unused imports, and eliminated all compiler warnings.
