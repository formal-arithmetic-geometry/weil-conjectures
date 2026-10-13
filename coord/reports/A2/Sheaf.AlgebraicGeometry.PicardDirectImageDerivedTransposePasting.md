## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_pasting` by a
factorization and naturality argument. Its signature and docstring are unchanged.
The proof factors each transpose as pullback of the normalized test section
followed by the coefficient transpose. Naturality of the derived square
comparison moves the section outside coefficient pasting. The final equality
then follows by functoriality and the normalized restriction equation.

Added three modules, each with one public theorem:

- `Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting` states the
  coefficient counit pasting step without a test section or structure-sheaf
  normalization. Its named theorem remains sorry.
- `Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization` states
  the one-square adjunction factorization, without any second square or restriction.
  Its theorem is proved from Hom-equivalence naturality and reassociation.
- `Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition` proves the
  structure-sheaf normalization step. It uses canonical single-pullback
  composition, a proved private naturality calculation, and a proved private
  ordinary unit-composition calculation. The private calculations follow the
  existing private proofs in CanonicalSinglePullbackSquare and
  PullbackStructureUnitSquare, with no edits to those modules.

The proof retains the theorem's original let-bound coefficient comparisons.
A proved private lemma, `pasteWithSection`, supplies the naturality and
reassociation calculation for abstract categories, without expanding scheme
constructions. The two new real definitions, `picardCoefficientTranspose` and
`picardDerivedUnitNormalization`, name the explicit constructions previously
repeated in the component statements. Their data contain no sorry and agree
with the corresponding constructions in the unchanged transpose definition.
No custom elaboration tactic is used.

Updated the parent node to the coefficient/source separation. Added the nodes
for the three new public theorems and two explicit constructions. No existing declaration signature, definition,
public import, target statement, unit record, or chapter record changed.

Local compilation used unchanged source copies, now retained only in
`scratchpad/baseline`, of DerivedPullbackComposition,
CanonicalSinglePullbackSquare, PicardDirectImageDerivedTranspose,
PullbackStructureUnitSquare, and SchemeDerivedMateEvaluation;
they are not adaptations or changes of this delivery.

## Proved and sorry left

Closed the item's one local hole:
`AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_pasting`
(node `lem-sc-picard-direct-image-derived-transpose-pasting`).

Added and proved
`AlgebraicGeometry.Scheme.picardDerivedUnitNormalization_comp`
(node `lem-sc-picard-derived-unit-normalization-composition`). Its module has
no sorry, including in its private helpers.

The delivery adds exactly one sorry:
`AlgebraicGeometry.Scheme.picardCoefficientTranspose_pasting`
(node `lem-sc-picard-coefficient-transpose-pasting`). Its proof is exactly
`:= by sorry`, and its docstring and node give the coefficient counit argument.
Also added and proved
`AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_factorization`
(node `lem-sc-picard-direct-image-derived-transpose-factorization`). This
one-square identity isolates only adjunction naturality, with no successive
base change, no second scheme map, and no normalized restriction. The proof
expands the explicit constructions and applies a proved private abstract
Hom-equivalence naturality calculation.

This is a decomposition: one upper hole closed, one strictly smaller coefficient
hole added, net zero holes closed. It is not a claim that the target's entire
import closure is proved. The remaining coefficient step excludes the test
section, its conjugated restriction, and all source unit-normalization maps;
the item supplies the actual argument adding those parts back. The private
abstract naturality calculations are fully proved, as are both private helpers
of the normalization theorem.

The new statements were checked on identity morphisms and reflexive equality
transports, arbitrary nonflat maps, zero coefficients, and empty schemes.
Only comparisons for the structure sheaf are inverted. There is no assumption
of invertibility of the coefficient single-pullback maps or of base change.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`: already available through
  the unchanged public statement imports; its node and module remain needed.
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare`: used by the
  remaining coefficient step and imported there, rather than by the item's glue;
  its node and module are retained in the coefficient route.
- `Sheaf.AlgebraicGeometry.PullbackStructureUnitSquare`: neither new statement
  nor the item's proof uses the square theorem. The normalization proof performs
  the simpler ordinary composition calculation directly. Thus node
  `lem-sc-pullback-structure-unit-square` and this module are no longer needed
  by this item's proof route. Other users may still need them.

The original dependencies `lem-pc-module-pullback-adjunction` and
`def-pc-derived-base-change-map` remain required by the coefficient theorem;
they are not globally pruned. No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt introduced a theorem with the complete original
statement under an auxiliary name and left it sorry. That was a restatement,
not a reduction, and has been removed. Finding no short proof was insufficient
reason to abandon.

The parent plan combined coefficient and source normalization calculations in
one prose step. Separating them gives strictly smaller intermediate statements
and an actual Lean composition argument. No false mathematical statement or
necessary interface correction was found.

## New nodes

`lem-sc-picard-coefficient-transpose-pasting`, in
`dag/nodes/sec-abelian-varieties/`, states only the coefficient counit pasting
identity. The transpose is constructed explicitly from the fixed base-change
map and its coefficient comparison, with no new chosen data. Its proof plan
uses derived mate evaluation, composition coherence, canonical single-pullback
square compatibility, and uniqueness of the ordinary/tensor left adjoints.

`lem-sc-picard-derived-unit-normalization-composition`, in the same directory,
states and proves composition of the derived structure-sheaf normalization.
It has no fibre product, direct image, coefficient module, or test section.
The recorded proof is the forward normalization calculation followed by
cancellation of the two invertible structure-sheaf normalizations.

`lem-sc-picard-direct-image-derived-transpose-factorization` states the
one-square factorization of the normalized transpose through the coefficient
transpose. Its complete Lean proof is ordinary Hom-equivalence naturality and reassociation;
its statement has no successive-base-change data.

`def-sc-picard-coefficient-transpose` records the actual coefficient transpose
construction. `def-sc-picard-derived-unit-normalization` records the actual
structure-sheaf normalization composite. Both are real Lean definitions and
introduce no postponed data.

All new nodes inherit the parent's chapter, unit, and nearest blueprint ancestor. The
three required kinds of Mathlib search were run; LeanSearch returned an internal
server error and is recorded as unavailable, while LeanFinder and source grep
found component lemmas but no exact statement. Blueprint searches for "pullback structure sheaf composition",
"coefficient transpose", and "derived unit normalization" returned no matching
blueprint node. A source search for "normalized transpose factorization"
likewise found no existing blueprint node.
No change record is needed because no existing interface changes.

## Second reading by A2

1. Interface preservation: diffed every delivered module against the repository.
   Only PicardDirectImageDerivedTransposePasting exists there; its theorem signature
   is byte-for-byte identical, including the derived-category instance, arbitrary
   coefficient L, both projection equations, the test section, and every let-bound
   comparison. Its docstring and sole public import are unchanged. The other three
   modules are new. No existing definition, target, or external module is adapted.
   Verdict: pass.
2. Proof integrity: read pasteWithSection, transpose_three_maps, both normalization
   helpers, and all public constructions. The glue uses square naturality at
   e.inv followed by the section, coefficient pasting at Lt(E), and normalization
   at O_W. The factorization applies homEquiv_naturality_left_symm to the exact
   B of the original definition. The normalization proof derives the forward
   equation from canonicalSinglePullbackComposition, ordinary unit composition,
   and naturality, then cancels isomorphisms. There is exactly one local sorry,
   picardCoefficientTranspose_pasting, with no partial-proof or definition holes.
   No forbidden declaration or kernel-bypass mechanism occurs. The new definitions
   explicitly assemble existing maps; their adjunction choices preserve the pinned
   universal properties rather than selecting arbitrary objects. Verdict: pass,
   subject to the compilation and axiom results recorded below.
3. Remaining statement: read its complete Lean signature, node and docstring,
   against Stacks Tags 08HY (the counit-defined mate) and 0D5S (composition).
   It isolates pasting at the coefficient E, without any section, restriction,
   structure-sheaf normalization, or assertion that coefficient comparisons are
   invertible. Projection uniqueness gives j followed by a_t equals a_tprime;
   counit naturality, derived associativity, and the single-pullback square
   identify the output comparison. Identity maps and reflexive transports reduce
   to counit identities; zero coefficients give zero maps; empty schemes and
   nonflat maps add no condition because only structure-sheaf comparisons are
   inverted elsewhere. Independently searched LeanFinder for counit mates of
   composite squares, Loogle for inverse Hom-equivalence naturality, and rg in
   Sheaf, WeilConjectures and Mathlib. mateEquiv_square and mateEquiv_vcomp are
   generic ingredients, not the stated identity for the fixed single comparisons.
   No duplicate statement was found. Closing the remaining coefficient coherence
   requires a substantial transport calculation, not a few-minute application.
   Verdict: a valid strictly smaller split; one closed hole and one added hole
   remain a decomposition with net zero, not a complete proof of the closure.
4. Route and pruning: checked dag/units/sk-prop-av-cube.json and the old five
   proof dependencies. Its realized fields contain no node for this subordinate
   calculation and are unchanged; the theorem-of-cube route is preserved.
   Derived composition, module pullback adjunction, derived base change and the
   canonical single-pullback square remain in the transitive coefficient route.
   The ordinary structure-unit square is replaced by its elementary composition
   calculation; it is the only old node retired from this route. All three removed
   direct imports and all five old nodes are accounted for under No longer needed.
   Public imports in the new files supply names or instances used in signatures
   or public definitions; notably the Opens finality instance is needed to build
   the structure-unit isomorphism. The single-pullback composition import is
   proof-only. Verdict: pass; no additional pruning justified.
5. DAG agreement: checked all six delivered node records, their Lean declaration
   text, proof steps, proof_deps unions, source, origins, creation records and
   blueprint ancestry. Every recorded Lean statement occurs verbatim in its file;
   every proof_deps list equals the union of step uses. The coefficient node
   records the outstanding counit/coefficient calculation, and the two proved
   helper nodes record the actual naturality and normalization reductions.
   Definition nodes have empty proofs and describe explicit constructions.
   Verdict: pass.

Second reading changed the report only: added this independent review, clarified
which old dependency is actually retired, and recorded independent searches and
validation. No proof or interface repair was required.

Local validation: the three new modules compiled cleanly in import order
(43.2 s, 59.1 s, 34.8 s). The main module timed out once, then compiled cleanly
on its own in 56.0 s against those outputs, within the unchanged 60-second limit.
No code change or limit increase was used to obtain that result.

A scratch copy of the actual delivered main proof with #print axioms commands
compiled in 54.6 s. The factorization, normalization theorem, coefficient
construction and normalization construction use only propext, Classical.choice
and Quot.sound. The main theorem and the coefficient-pasting theorem additionally
use sorryAx, exactly as expected from the remaining named coefficient hole.
No other axiom occurs. The scratch copy is not delivered. Final verdict for
point 2: pass as a decomposition, with its remaining dependency explicit.
