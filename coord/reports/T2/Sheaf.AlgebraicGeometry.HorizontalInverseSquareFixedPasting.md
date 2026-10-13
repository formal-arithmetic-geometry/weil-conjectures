## What changed

Replaced the hole in `AlgebraicGeometry.horizontal_inverse_square_fixed_pasting`
with a complete Lean reduction. Three proved private helpers compute the inverse
mate of transported right-adjoint uniqueness, compute the canonical ordinary
transfer square, and identify these squares for the pinned scheme comparisons.
The final proof substitutes this equality into geometric ordinary pasting.

Added the proof-only import
`Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting`. Its new theorem
isolates geometric pasting before the supplied right adjoints `c`, `d` and their
adjunctions are introduced. Existing public signatures and imports are unchanged.
Updated the item's proof plan to match the Lean proof.

Sources checked: [Stacks Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM),
ordinary horizontal base-change composition, and
[Stacks Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR), its use for second
mates. Mathlib's adjunction uniqueness and mates files supply the categorical
calculation. Existing derived pasting handles upper-left morphisms rather than
this horizontal diagram; the rectangle comparison supplies unspecified direct
comparisons, so neither directly gives the fixed geometric comparison here.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.horizontal_inverse_square_fixed_pasting`
(node `lem-sc-horizontal-inverse-square-fixed-pasting`). Its signature is unchanged.
The categorical helpers `transport_mate`, `canonical_transfer_app` and
`fixed_transport_mate` are fully proved and contain no holes.

Added one hole:
`AlgebraicGeometry.horizontal_ordinary_inverse_fixed_pasting`
(node `lem-sc-horizontal-ordinary-inverse-fixed-pasting`), in its own new module.
Its entire proof is `by sorry`, with source and proof in words in the docstring
and DAG node. It has none of the supplied upper right-adjoint data and no inverse
mate of their uniqueness comparison. The proved categorical transport is the
part needed to pass from this lower geometric statement to the original theorem.

This is a decomposition: one original hole closed, one lower hole added, net zero.
There are no remaining holes in the item's module. No arbitrary data is selected
from a new existence statement. The geometric statement includes identity maps,
empty schemes and zero complexes: its comparisons are fixed natural isomorphisms,
and cancellation uses only the three explicitly assumed ordinary isomorphisms.

## No longer needed

No existing import was removed and no existing dependency module is claimed
pruned. The direct uses of `def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition` are now in the lower geometric
node, so these remain needed in the import closure. Both public imports remain needed by the statements.

Discarded the earlier attempt's unsubmitted pointwise node
`lem-sc-horizontal-inverse-square-fixed-pasting-pointwise`; it is not delivered.
The unused earlier scratch modules `HorizontalOrdinarySquareFixedPasting` and
`QCohInverseBaseChangeCancellation` are not imported or delivered.

## Where the brief, the DAG or earlier work was wrong

The previous pointwise decomposition was a restatement of the original theorem,
not a strictly smaller part. Its rejection was correct. This delivery instead
proves the categorical adjoint-transport part and leaves only geometric pasting.
The earlier ordinary node's prose repeated its final clause several times;
that unsubmitted text is repaired.

The earlier compiler timeout was avoidable. Keeping wrapper definitions folded,
simplifying the identity isomorphism after eliminating the projection equality,
and using explicit definitional conversion for the final equality makes the
proof compile within the single-file limit. No definition or statement changes
were necessary. The unit's realized statement and steps are unchanged.

## New nodes

`lem-sc-horizontal-ordinary-inverse-fixed-pasting` is the ordinary geometric
part of the original plan, without the supplied projection right adjoints. It
records the transposition proof of forward horizontal pasting, the fixed
scheme-isomorphism transport, and inversion of the three ordinary squares.
Its module is `Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting`.
No change records or forced adaptations are needed.

## Second reading by T2

1. Compared the delivered item with the repository using `diff -u`, and checked
   its existing theorem signature byte for byte. The existing signature,
   docstring, public imports and definitions are unchanged. The only new import
   in the item is proof-only. No change record or forced adaptation is required.
2. Compiled both delivered modules in import order through `lcompile.py`: clean,
   with no errors or warnings. Inspected every proof and scanned for forbidden
   declarations: the only hole is the named geometric theorem reported above;
   there are no data definitions or arbitrary existence witnesses in this
   delivery. The categorical transport proof expands mates and uses uniqueness,
   naturality and the triangle identity; the final proof substitutes its proved
   square equality into the geometric equation. Scratch `#print axioms` checks
   cover the original theorem, all three helpers and the new theorem: only
   propext, Classical.choice and Quot.sound occur in the generic helpers; the
   scheme specialization, original theorem and open geometric theorem also
   depend on sorryAx from still-open statements. No other axiom occurs.
3. Read the new statement, its full docstring proof and node together. Its
   transfer component is li followed by pushforward of the inverse equivalence
   unit, with the correct direction. Forward pasting followed by inversion of
   the three assumed ordinary squares gives the displayed equation. Identity
   base maps reduce to the comparison unit laws, zero complexes give the zero
   morphism identity, and empty schemes require no nonemptiness assumption.
   Verified the source against Stacks [0ATM](https://stacks.math.columbia.edu/tag/0ATM)
   and [0ATR](https://stacks.math.columbia.edu/tag/0ATR). This is a strictly smaller
   geometric part of the original argument: supplied projection right adjoints
   and the inverse mate of their uniqueness comparison have been eliminated by
   a fully proved categorical calculation. It is a decomposition, with net zero
   holes closed, rather than a complete axiom-free proof of the original item.
4. Repeated searches with different terms: LeanFinder for Beck--Chevalley
   composition under pullback associativity, Loogle for right-adjoint uniqueness
   and counits, and grep for conjugate composition and whiskering. These find
   the uniqueness lemma already used and underived comparison tools, not the
   fixed derived QCoh equation. Also inspected `DerivedBaseChangePasting`,
   `RectangleOrdinaryGeometricComparisons` and its direct-image dependency. The
   first treats an upper-left morphism; the others leave the direct and base
   comparisons existential and do not identify these fixed comparisons. No
   short closure of the geometric hole follows from them. Both public imports
   are needed in the signatures; the new private import is used by the proof.
   Of the old proof dependencies, `def-pc-derived-base-change-map` and
   `lem-pc-ringed-spaces-derived-pullback-composition` move to the new geometric
   node and are no longer direct proof dependencies of the item; neither is
   pruned from the import closure. The other two old dependencies remain. The
   unit `sk-thm-picard-duality` and its `realized` fields are unchanged; this
   reduction stays below its route.
5. Checked both DAG Lean statements verbatim against the delivered declarations,
   the proof-step dependency unions, the proof origins, and the new node's
   source, searches, creation, blueprint, chapter, unit and Lean fields. They
   agree with the delivered proof and the remaining geometric obligation.

Second reading changed only this report: recorded the independent review,
additional searches, source verification, edge-case reasoning and the explicit
old-dependency accounting. No Lean or DAG repair was needed.
