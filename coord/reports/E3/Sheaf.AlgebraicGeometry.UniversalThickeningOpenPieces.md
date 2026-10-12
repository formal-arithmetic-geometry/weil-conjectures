## What changed

Proved `AlgebraicGeometry.universalFirstOrderThickening_open_pieces` in
`Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`, with its signature unchanged.
The proof follows all three clauses and the original eight-step DAG route.

Two proved private helpers establish surjectivity of a square-zero closed immersion
and preservation of square zero under open restriction. Surjectivity follows from
Mathlib's equality of the kernel support with the closed image and invariance of
support under positive powers. Restriction follows by evaluating the squared
ideal on affine opens and using `Scheme.ker_morphismRestrict_ideal`.

The open correspondence is the order isomorphism of opens induced by the underlying
homeomorphism. For universality on an open, the proof restricts the immersion and
structure morphisms, applies the original universal property, and factors the lift
through the open using surjectivity of the test thickening. Cancellation of the
open inclusions gives compatibility and uniqueness. For base enlargement, it
factors the test structure morphism through the open base and applies universality
there, again proving uniqueness by cancellation.

No statement, definition, public visibility, or target changed. No new module or
node was required. The existing DAG proof already describes this route, so its
node is unchanged. The source's general remarks were checked at
https://stacks.math.columbia.edu/tag/04F3 (the repository's cited TeX is absent on
this machine).

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.universalFirstOrderThickening_open_pieces`
(node `lem-weil-pbc-universal-thickening-open-pieces`).

The module has zero remaining `sorry`s. Added zero holes and split off zero
statements. Both private helpers are proved. A compiled `#print axioms` check
reported exactly `propext`, `Classical.choice`, and `Quot.sound` for the public
theorem. No holed library theorem is used.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.Thickening`; its definitions remain available through
`Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`, which is required by the
public statement. No module leaves the target import closure from this removal.
No original DAG proof dependency is pruned: the proof follows the existing plan.

The existing `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore`
theorem was considered and used during development, then replaced by a direct
proof; it is absent from the delivery's imports. This is not a claim that the
module can be pruned from other consumers.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The DAG's elementary assertion that a
first order thickening is a homeomorphism requires a square-zero support argument
because `IsFirstOrderThickening` does not explicitly include surjectivity; the
proved private helper supplies that argument without changing the definition.

## Second reading by E3

1. **Interface: pass.** Compared the delivered module with the repository using
   `diff -u`, and separately compared the existing theorem's signature as raw
   text through `:= by`: byte-for-byte identical. The only changes are removal
   of a redundant plain import, two private proved helpers, and the theorem's
   proof. No definition, public signature, visibility, or target changed;
   no change record is required.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.universalFirstOrderThickening_open_pieces`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read both helpers and all three clauses. There is no `sorry`, forbidden
   declaration, hollow definition, or selection of data from an unproved
   existence statement. Open factors use Mathlib's actual lift construction;
   extensions come from the assumed universal property.
3. **Split statements: pass (none).** No statement or node was split off.
   The private helpers are proved and express only surjectivity and preservation
   of square zero under open restriction. Checked the empty source/target and
   empty/whole open cases: support of the zero ideal is the whole space,
   the homeomorphism gives the empty/whole open correspondence, and all image
   containment arguments remain valid without an inhabitedness assumption.
   Searched the project, upstream algebraic-geometry sources, and Mathlib for
   first-order restriction/surjectivity and universal open restriction. The
   existing open-restriction core has `sorry`; using it would retain a hole.
4. **Route and pruning: pass.** The direct proof uses the recorded Mathlib
   leaves for restriction of the kernel ideal and factorization through an
   open immersion. All eight DAG steps are present, including both uniqueness
   arguments by cancellation. The sole public import supplies the definitions
   in the signature; no proof-only public import remains. The removed plain
   `Thickening` import is redundant through `UniversalFirstOrderThickening`.
   No original proof dependency is unused or pruned. Inspected
   `dag/units/sk-thm-p1.json`, including `realized`: this below-unit lemma does
   not bypass any realization of the unit statement or its steps.
5. **DAG agreement: pass.** Read the item's node and the recorded Mathlib matches
   of its restriction and open-factorization dependencies. They are precisely
   the declarations used by the proof. Definitions account for the remaining
   dependencies; the over-base conditions are expressed by the commuting
   morphisms. The original `proof`, `proof_deps`, and `proof_origin` remain
   accurate. Checked the general remarks in Stacks Tag 04F3, paragraphs on
   restriction and enlargement of the open base, against the two universality
   arguments: https://stacks.math.columbia.edu/tag/04F3.

Second-reading changes: appended this review only. No repair to the Lean proof,
imports, or DAG was needed. Independently confirmed one original hole closed,
zero holes added, and zero split-off statements.
