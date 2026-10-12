## What changed

The proof-only API/import change is recorded in `coord/changes/popescu-desingularization-quotient-data.md`.

`Sheaf.RingTheory.PopescuDesingularizationQuotientData` now proves
`Algebra.exists_desingularization_quotient_data` with its signature and public imports
unchanged. It constructs `S = R[v,w]/(g)` and the image ideal `K` of the substituted
relations. The proof derives finite presentation from finite generating families,
maps the divisibility and quadratic relation through the quotient, constructs both
algebra maps by quotient descent, and proves their composite is `α`.

Evaluation at `v=0`, `wᵢ=πλᵢ` kills `g` by three explicit applications of annihilator
stability. No cancellation by a zero divisor is used. At a prime containing `π`, the
selected Jacobian matrix reduces to the identity. Localizing at its determinant and
composing pre-submersive presentations gives a standard smooth presentation directly.
Smoothness implies flatness of this neighbourhood; a further localization and flatness
transitivity give flatness of `S_q`. These two private helpers are completely proved.

Two proof-only imports introduce new intermediate theorem modules:
`Sheaf.RingTheory.PopescuDesingularizationSubstitution` and
`Sheaf.RingTheory.PopescuDesingularizationInvertedQuotient`.
The existing strictly standard localization theorem supplies smoothness of `A_π`.
The updated parent DAG node follows the actual proof, including the direct Jacobian
argument. No definitions, existing statements, visibility, or downstream modules change.
There is no choice-based definition: the witnesses are eliminated inside the existential
theorem proof, and the quotient rings and algebra maps are constructed explicitly there.

## Proved and sorry left

Closed the item's only hole:
`Algebra.exists_desingularization_quotient_data`
(`lem-weil-pbc-popescu-desingularization-quotient-data`). No `sorry` remains in the item.

Added two strictly intermediate holes, each the entire proof of a public theorem in
its own new module:

- `Algebra.exists_desingularization_substitution`
  (`lem-weil-pbc-popescu-desingularization-substitution`): only polynomial presentation
  and substitution identities. It has no annihilator hypothesis, Noetherian hypothesis,
  quotient factorization, or smoothness conclusion.
- `Algebra.desingularization_inverted_quotient_equiv`
  (`lem-weil-pbc-popescu-desingularization-inverted-quotient`): a purely algebraic
  isomorphism for a specified presentation and specified substitution. It has no
  strictly standard, section, Noetherian, or annihilator hypotheses.

This delivery is a decomposition: one upper hole closed, two lower holes added, rather
than a sorry-free proof of the full construction. The private local Jacobian and
flat-localization helpers, all quotient glue, and annihilator cancellation are proved.
The existing `Algebra.smooth_localizationAway_of_isStrictlyStandardElement` remains an
imported dependency; its hole is unchanged by this delivery.

The original and all new modules compile cleanly through `lcompile.py`.
Temporary `#print axioms` probes confirm that both private helpers use only
`propext`, `Classical.choice`, and `Quot.sound`. The parent theorem uses `sorryAx`
through its named open dependencies, as expected for this decomposition.

The earlier delivery-tool import mismatch is resolved in the current tool installation.
The second reader reruns the prescribed dry run and delivery below.

## No longer needed

No original public imports are removed: all five belong to the unchanged statement
interface. Removed proof-only imports are
`Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`,
`Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`,
`Sheaf.RingTheory.EquationCountFibreDimensionFlat`,
`Sheaf.RingTheory.StandardSmoothDimensionAtPoints`, and
`WeilConjectures.Mathlib.Topology.KrullDimension`. The matrix dependency is now imported
by the substitution intermediate, and quotient/localization commutation by the
inverted-quotient intermediate. These two imports are proof-only. The original plan's following branches are unnecessary for this
proof and are removed from the parent node's proof dependencies:

- `lem-weil-pbc-presentation-base-change` (Mathlib presentation base change).
- `lem-weil-pbc-standard-smooth-over-field-dimension-at-points`
  (`Sheaf.RingTheory.StandardSmoothDimensionAtPoints`).
- `def-kun-dimension` and `def-kun-topological-dimension-at-point`
  (`WeilConjectures.Mathlib.Topology.KrullDimension`).
- `lem-weil-pbc-equation-count-fibre-dimension-flat`
  (`Sheaf.RingTheory.EquationCountFibreDimensionFlat`).
- `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime`
  (`Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`).
- `def-weil-pbc-smooth-ring-map` as a separate parent proof edge; the unchanged statement
  already imports Mathlib's smoothness definitions.

The matrix-left-inverse, formal-derivative, and localization-quotient-commutation edges
move to the appropriate new intermediate nodes. They are not claimed as globally
pruned: the substitution proof still needs the first two, and the inverted quotient
proof still uses quotient/localization commutation. The dimension and smooth-fibre
branches above are bypassed only below the unit level; the `sk-thm-p1` statement and
all its realized steps remain unchanged. No claim is made that a branch needed by
other parent modules is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or signature change was necessary. The original fibre-dimension
route is longer than needed: an explicit Jacobian minor already witnesses a smooth
neighbourhood of every prime containing `π`.

The checkout does not contain `literature/stacks-project/smoothing.tex` at its recorded
path. The complete primary-source proof was read at
https://stacks.math.columbia.edu/tag/07CR, including the substitution and the inverted
quotient paragraph. The source reference in the nodes remains the project's canonical
reference. Searches were made using `msearch.py` and are recorded in `searches.jsonl`:
LeanSearch was unavailable (Internal Server Error), while LeanFinder, Loogle and
Mathlib source searches returned ingredients, not the new intermediate statements.
A search of the entire imported blueprint for desingularization found no duplicate
blueprint node for either intermediate.

Edge cases were checked before stating the intermediates: `c=0` gives the empty
Jacobian determinant one and no `g` relations; `n=0` and `m=0` permit empty polynomial
families; inverting `π=0` gives zero rings on both sides of the proposed isomorphism;
`π` a unit makes the local-prime assertion vacuous; no regular-element assumption is
needed for any polynomial identity. The coefficientwise construction in the first
intermediate avoids cancelling `π³`. The lifted variable set ensures the quotient has
universe `Type (max u w)` without exporting an arbitrarily chosen object.

## New nodes

`lem-weil-pbc-popescu-desingularization-substitution`, in
`dag/nodes/sec-proper-base-change/`, realizes the polynomial portion of steps 1–5 and
the ideal-square observation of step 8. Its module is
`lean/Sheaf/RingTheory/PopescuDesingularizationSubstitution.lean`. It records a complete
proof from the translated presentation, constant minor identity, scalar left inverse,
and coefficient expansion, with the existing nodes for those ingredients.

`lem-weil-pbc-popescu-desingularization-inverted-quotient`, in the same chapter,
realizes the algebraic identification in step 7. Its module is
`lean/Sheaf/RingTheory/PopescuDesingularizationInvertedQuotient.lean`. Its proof describes
both elimination orders and the inverse maps. Its hypotheses fix every ring and
substitution involved; the parent combines this isomorphism with existing smoothness
and composition results. Both new nodes inherit the original unit and blueprint
ancestor. No change record is needed because no existing interface is changed.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading.

## Second reading by V1

1. **Existing interface — pass.** Compared the parent module against the repository
   before the delivery tool prepared its commit. The existing theorem signature is
   byte for byte unchanged; all five public imports and its visibility are unchanged.
   No existing definition is changed, and no downstream adaptation is delivered.
2. **Kernel proof — pass.** Independently compiled all three modules through
   `lcompile.py --all`. The parent has no `sorry`; the two new public theorems have
   exactly the reported whole-proof `sorry`s. Scanned for prohibited declarations
   and hidden holes. A scratch-copy `#print axioms` confirms only `propext`,
   `Classical.choice`, and `Quot.sound` for both private helpers, and additionally
   `sorryAx` for the parent through its named open dependencies. Quotient rings,
   ideals and maps are explicit local constructions inside an existential proof;
   no definition exports data chosen from an unproved existence theorem.
3. **Split statements — pass.** Read each new signature and complete proof docstring
   against [Stacks Tag 07CR](https://stacks.math.columbia.edu/tag/07CR). Substitution
   covers only polynomial identities; the inverted quotient covers only the
   specified algebraic isomorphism. Neither restates the parent. Checked zero and
   unit parameters, zero rings, empty variable/relation families, and zero divisors:
   division is coefficientwise, never cancellation of the parameter. Independent
   LeanFinder and Loogle searches used different queries; source searches for
   rescaling, variable changes and quotient equivalences found ingredients only.
   Neither open statement can be closed in a few minutes from the available API.
4. **Route and pruning — pass after report repair.** The parent combines both
   intermediates with proved quotient glue, annihilator stability, and a direct
   Jacobian smooth-neighbourhood argument. Mathlib supplies standard smoothness,
   flatness and localization composition. The unit `sk-thm-p1` realized statement
   and every realized step remain in place; only the route below that level changes.
   Corrected the report to list the five removed proof-only imports explicitly.
   Dependencies transferred to the new nodes are not claimed globally pruned.
5. **DAG — pass after documentation repair.** The parent proof steps and dependency
   union follow the actual Lean reduction. Both new nodes have their statements,
   sources, proof steps, provenance, searches, creation data, blueprint ancestry,
   unit/chapter and Lean records. Added the omitted explanation that the chosen
   lift of the parameter differs from the constant polynomial by a relation-ideal
   element, so replacing it changes a relation product only by an ideal square.

Changes by this reader: added proof-only imports of the scalar-left-inverse and
localization/quotient ingredients to the intermediate modules, clarified the lift
replacement in the substitution docstring and node, recorded the independent
searches, corrected the removed-import report, and replaced the stale tool-failure
paragraph. No theorem signature, definition, or existing proof body was changed.
The two lower holes remain; this is a decomposition (one closed, two added), with
net minus one hole before any shared-import pruning, not a sorry-free proof.
