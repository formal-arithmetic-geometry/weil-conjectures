## What changed

Proved `AlgebraicGeometry.singleComplex_nested_coefficient_coherence` by combining
two new, proved formal laws in
`Sheaf.AlgebraicGeometry.CoefficientSquarePasting` and
`Sheaf.AlgebraicGeometry.CoefficientSquareCoordinateChange`. Added both as
proof-only imports. The original statement, definitions, visibility and public
imports stay identical.

The pasting law compares two successive coefficient squares with their
rectangle; the coordinate-change law compares two coordinates for one square.
Both are proved from the chosen composition comparison's existing associativity
and naturality, with private proved helpers for the preceding comparison maps.
Equality-transport naturality and proof irrelevance identify the transports.
The final coefficient morphisms are handled by naturality. The original theorem
proves rectangle commutativity from the two pullback conditions, cancels the
source comparison, applies coordinate change and appends the inverse target
comparison.

Named local maps keep elaboration from expanding the full chosen derived
comparison throughout the goal. Used the comparison-elaboration options already
used by neighboring modules. The unchanged statement has an unused `KW'` let;
a theorem-scoped `linter.unusedVariables` option suppresses that existing binder
warning without changing its statement. No new definitions or arbitrary data
choices were introduced. Updated the original node's proof and added the two
supporting nodes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.singleComplex_nested_coefficient_coherence`
(`lem-pc-single-complex-nested-coefficient-coherence`).

Also proved both new supporting statements:
- `AlgebraicGeometry.coefficient_square_pasting`
  (`lem-pc-coefficient-square-pasting`).
- `AlgebraicGeometry.coefficient_square_coordinate_change`
  (`lem-pc-coefficient-square-coordinate-change`).

One original hole closed; zero holes added. No `sorry` remains in any of the
three delivered modules. Every private helper is proved. The proof still uses
the existing `exists_derivedPullbackComposition`, whose lower dependencies are
outside this item; no new unproved intermediate statement was added.

## No longer needed

None. `DerivedPullbackComposition` supplies the fixed comparisons used in every
statement, and `Mathlib.AlgebraicGeometry.Restrict` supplies `isoOfLE_hom_ι`.
No original module or node is pruned. The original direct proof dependency
`lem-pc-ringed-spaces-derived-pullback-composition` is replaced in the item
node by the two square-law nodes, but remains a statement dependency, a public
import, and a transitive proof dependency of both laws; it is still needed.
No base-change or direct-image lemma is imported by this coefficient-only proof.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's absence of an existing packaged coefficient identity was
not an obstruction. The original DAG expansion separates into square pasting
and square coordinate change; both can be stated and proved in Lean without
nested opens. The original theorem follows by the comparison cancellation
calculation. No original mathematical statement was changed or disputed.
Checked the composition statement in Stacks Tag 0D5S and source-open induction
in Tag 0DJ9. The new laws are formal consequences of the recorded associativity
and naturality, not geometric claims made verbatim by those tags. The blueprint
unit and its route stay unchanged.

## New nodes

`lem-pc-coefficient-square-pasting`:
`Sheaf.AlgebraicGeometry.CoefficientSquarePasting` proves compatibility of
coefficient restriction with pasting two arbitrary commutative squares. It has
no coordinate isomorphisms and does not restate the original nested-open result.

`lem-pc-coefficient-square-coordinate-change`:
`Sheaf.AlgebraicGeometry.CoefficientSquareCoordinateChange` proves compatibility
with changing the coordinates of one square. It has no iterated restriction and
even allows arbitrary coordinate arrows.

Both nodes retain the item's chapter and unit route and use the existing
`lem-pc-ringed-spaces-derived-pullback-composition`. LeanFinder, LeanSearch
(unavailable) and source grep were recorded; the Mathlib pseudofunctor tools do
not directly apply because no derived-pullback pseudofunctor is packaged here.
The proved identities include empty schemes, zero coefficients and identity
coordinate arrows, since the arguments use only functoriality, associativity,
naturality and invertibility of comparison maps. No change record is needed
because no existing interface changes.

## Second reading by N1

1. **Existing interface — PASS.** Read the diff against the repository module.
   The entire existing theorem signature, including all let-bound comparisons
   and coefficient maps, is byte-for-byte identical. No existing definition,
   public import, declaration visibility or target statement changed. Only
   proof imports, theorem-scoped elaboration/linter options and the proof body
   were added. There are no forced adaptations or statement-change records.

2. **Proof and axioms — PASS.** Independently compiled all three delivered
   modules in import order with lcompile.py --all: clean, without warnings.
   Read every private comparison helper and both public square-law proofs.
   A scratch copy with #print axioms for all three public theorems compiled;
   each depends on exactly propext, Classical.choice and Quot.sound, with no
   sorryAx. A source scan found no sorry, axiom, unsafe, opaque, implemented_by,
   extern or kernel-check bypass. No definitions or arbitrary existence-witness
   data were introduced. The selected comparison is the existing library
   comparison constrained by its left-derived universal property.

3. **Supporting statements — PASS.** No unproved statement was split off.
   Both new public laws are proved formal parts of the argument: pasting has
   two squares and no coordinate arrows; coordinate change has one square
   and no iterated restriction. Neither restates the nested-open target.
   Checked the identity-arrow/equal-open cases, empty schemes and zero
   coefficient morphisms against the formal calculations: they require no
   nonemptiness, geometric cancellation or nonzero coefficients. Coordinate
   arrows need not be isomorphisms. The rectangle equality follows from the
   other equations, so its explicit hypothesis is harmless and is proved at
   the use site. Both statements have complete proof docstrings and nodes.
   Independent LeanFinder search for natural-isomorphism coherence of
   contravariant rectangle restriction returned CatCommSq naturality laws;
   these express naturality of an already specified square, not coherence
   between the chosen comparisons. Loogle did not recognize
   eqToHom_naturality; source grep confirmed the actual Mathlib transport
   lemmas already used. Reviewed CatCommSq.hComp and
   Pseudofunctor.isoMapOfCommSq_eq; neither gives a shorter direct proof
   without first packaging the chosen derived comparisons as a pseudofunctor.
   No matching derived coefficient-square law occurs in either project root.

4. **Route and pruning — PASS.** The target specializes pasting, cancels the
   source composition comparison, specializes coordinate change and appends
   the inverse target comparison. Every delivered import is needed by a
   signature or proof. The original composition node remains needed in the
   signatures and through both square laws, though it is no longer a direct
   item proof dependency. No node or module is pruned. Read the unit record
   sk-thm-picard-semicon: its realized statement and step lists are empty;
   this delivery changes no unit record or chapter/unit route. The new laws
   are below the unit level. Checked the sources: [Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
   gives derived-pullback composition; [Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
   uses source-open induction. These square identities are the recorded
   formal associativity/naturality consequences, not verbatim Stacks lemmas.

5. **DAG agreement — PASS.** Mechanically compared each node's lean.statement
   to its theorem signature and checked proof_deps equals the union of the
   proof-step uses. Read the mathematical statements, proof steps and origins
   against the code. The original node names the two laws actually applied;
   both new nodes name the composition theorem actually used, with source,
   search records, creation data, blueprint origin, chapter/unit and Lean
   records. No existing node statement changed.

**Second-reading changes:** clarified under No longer needed that the old
composition proof dependency is retained transitively and as a statement
import; added this independent review and its compile/axiom/search evidence.
No Lean proof or statement repair was needed. One original hole closed,
zero holes added; both new supporting theorems are fully proved.
