## What changed

Replaced the proof of `AlgebraicGeometry.ConormalGradedAlgebra.exists_affineData`.
All its hypotheses, its conclusion and every field of `AffineData` are unchanged.
Existing public imports are preserved. Added proof imports for the existing ambient
associated-graded algebra, normalized power quotient, affine power multiplication,
power monicity, and the three new step modules listed below. No adopted source
module or existing definition was changed.

The proof constructs normalized isomorphisms from pushforward of each fixed
`piece i n` to the ambient quotient, using `closedImmersion_power_quotient` with
exponent one and exactly the adjunction used by `representative`. It descends the
ambient homogeneous operations and totalizes them. Injectivity of the quotient
isomorphism, the ambient representative product formula and monicity of the power
inclusion prove the required product formula for every specified representative,
on every ambient open. Evaluating the descended unit equation proves the constants
formula, also on every ambient open.

For affine charts the new input is only an additive equivalence for a module
coproduct. Quotient induction and the affine power range show that homogeneous
representatives additively generate. Double induction then proves multiplicativity
of that additive equivalence: use an affine product lift and the associated-graded
representative multiplication formula. The resulting ring equivalence gives the
required categorical ring isomorphism with the original representative normalization.
Thus multiplicativity of the affine comparison is proved here, rather than being
included in an existence assumption for a chart.

The unit's route is preserved: the normal cone uses the same direct sum of the
ideal-power quotients. The three new lemmas are below that unit. The current
blueprint places `sk-def-purity-conv` under `sec-six-functors-basics`; its normal-cone
definition and the inherited DAG unit record were read without changing either.
Stacks Divisors, the paragraphs before Definition 0630 and Lemma 0633, and Modules,
Lemma 08KS, supply the source argument. The new docstrings expand its omitted details.

Validation: all four sandbox modules compiled through `lcompile.py`. The final
warning-free compile of the item completed in 12.1 seconds. The three intermediate
modules compiled separately in the preceding import-order pass. No transparency
or linter option was disabled. Static checks confirm unchanged `AffineData`, exact
new-node signatures, matching proof dependencies and lines at most 100 characters.

## Proved and sorry left

Original holes: one. Closed in the item:
`AlgebraicGeometry.ConormalGradedAlgebra.exists_affineData`
(node `lem-pur-conormal-graded-algebra-construction`). The item itself has zero
remaining `sorry`s. Its private quotient normalization, power lift, additive
induction and multiplicativity helpers are proved.

Added holes, each the sole theorem of its new module:

- `AlgebraicGeometry.exists_gradedAlgebra_closed_descent`
  (`lem-pur-closed-immersion-graded-algebra-descent`). This is a generic descent of
  homogeneous operations through supplied pushforward isomorphisms; it provides
  no total algebra, coproduct or chart.
- `AlgebraicGeometry.exists_gradedSheafAlgebra_totalization`
  (`lem-pur-graded-sheaf-algebra-totalization`). This is a generic totalization of
  an already supplied homogeneous sheaf algebra; it involves no closed immersion,
  ideal, quotient representatives or affine comparison.
- `AlgebraicGeometry.ConormalGradedAlgebra.exists_conormalCoproduct_affine_addEquiv`
  (`lem-pur-conormal-coproduct-affine-add-equiv`). This compares only the additive
  sections of an arbitrary module coproduct; it assumes and constructs no ring
  multiplication or structure map.

This is a decomposition: one original hole closed, three holes added, net minus
two holes. It is not an unconditional proof of the conormal construction. None
of the new statements restates the entire original obligation. The Lean assembly
proves the representative formulas and the multiplicative ring comparison.

Edge cases: for the zero ideal, positive pieces vanish and the degree-zero piece
is the structure sheaf; for the unit ideal the closed subscheme is empty and all
piece sections and sums are zero. Degree zero is retained in every construction.
Zero rings and empty affine inverse images are allowed. No finiteness, regularity,
Noetherian, quasi-separatedness or nonemptiness hypothesis has been introduced.

## No longer needed

No existing public import was removed, and no existing module or node is claimed
pruned globally. All three original public imports remain used by the statements.
The original direct proof dependencies for fully faithful closed pushforward,
affine pullback sections and the tilde adjunction are now used by the new descent
and additive-comparison steps. They remain needed through those steps. The
sheaf-of-modules category and graded-sheaf-structure definition remain used by
totalization and descent. No downstream declaration was removed or weakened.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies supply the ambient homogeneous algebra and the normalized
quotient isomorphisms, but their Lean statements do not themselves supply descent
of bilinear operations, totalization as a ring sheaf with its module coproduct,
or the normalized additive coproduct comparison on an affine inverse image.
Those missing interface steps are now explicit, independently usable statements.
The original chart statement and representative normalizations are retained.

The blueprint-ancestor helper returns `None` for this item's `created.item` module
name. New nodes use the existing item's explicit blueprint anchor
`def-pur-normal-bundle`, with this item and its conormal-algebra parent in `via`.
No launcher file or shared repository file was modified.

## New nodes

`lem-pur-closed-immersion-graded-algebra-descent` is stated in
`Sheaf.AlgebraicGeometry.ClosedImmersionGradedAlgebraDescent`. Its source is the
closed-support module equivalence (Modules 08KS) applied to graded operations,
as used immediately before Divisors 0630. The supplied isomorphisms determine the
operations, and the unit equation includes the actual structure-sheaf map.

`lem-pur-graded-sheaf-algebra-totalization` is stated in
`Sheaf.AlgebraicGeometry.GradedSheafAlgebraTotalization`. Its source is the
finite-support graded algebra and sheafification construction used in Divisors
0630 and Cohomology of Schemes 087Z. Its coproduct is in sheaves of modules;
sections on arbitrary opens are not asserted to commute with infinite sums.

`lem-pur-conormal-coproduct-affine-add-equiv` is stated in
`Sheaf.AlgebraicGeometry.ConormalCoproductAffineAddEquiv`. It isolates only the
additive affine assertion of Divisors 0633(2), using normalized affine pullback
and the tilde adjunction. It applies to any specified module coproduct.

Each node has its Lean statement, full proof in words, source, actual logged
Mathlib searches and the inherited chapter/unit. No change record is required:
there is no change to an existing statement, definition or public interface.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
