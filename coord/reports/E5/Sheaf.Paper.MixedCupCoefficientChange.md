## What changed

Replaced the sole `sorry` in
`WeilConjectures.MixedCupCoefficientChange.mixedCupCoefficientChange` with a complete
Lean assembly of three strictly smaller steps. The original theorem signature,
`Comparisons` structure, separation instance, existing docstrings, options and
public imports are unchanged. Three private proof imports connect the new modules:

- `Sheaf.Paper.MixedCupOperationComparisons`: existence of normalized point and
  cohomology isomorphisms, with identities and formal composition.
- `Sheaf.Paper.MixedCupTensorComparisons`: independent existence of normalized
  site tensor isomorphisms, with naturality and formal identity/composition.
- `Sheaf.Paper.MixedCupCoefficientSquare`: the cup square for given families
  satisfying every normalization and coherence hypothesis from the first two steps.

The final proof obtains both families by existential elimination, fills every
field of `Comparisons`, and applies the third theorem, explicitly supplying all
normalization and coherence proofs. No definition selects arbitrary data from an
unproved existence theorem. No new definitions, structures, instances or public
imports are introduced. The main DAG node now follows this exact three-step route.
Each new module contains one public theorem with its whole proof `by sorry`.

## Proved and sorry left

Original holes: 1. Closed in the item module:
`WeilConjectures.MixedCupCoefficientChange.mixedCupCoefficientChange`.

Added holes, each in a separate new module with its own node:

- `WeilConjectures.MixedCupCoefficientChange.operationComparisons_exists`
  (`lem-sf-mixed-cup-operation-comparisons`).
- `WeilConjectures.MixedCupCoefficientChange.tensorComparisons_exists`
  (`lem-sf-mixed-cup-tensor-comparisons`).
- `WeilConjectures.MixedCupCoefficientChange.normalizedCup_coefficient_square`
  (`lem-sf-mixed-cup-square`).

This is a decomposition, not a completed mathematical proof or a net reduction:
one hole closed, three added, net minus two. No `sorry` remains in the item module.
The separation instance was already proved and is not counted as a new proof.
The operation lemma asserts neither a tensor comparison nor a cup square; the
site tensor lemma asserts neither cohomology comparisons nor a cup square; the
square lemma constructs no comparison data. Thus no new theorem restates the
original existence of the complete `Comparisons` package.

## No longer needed

No existing public or proof imports were removed. No existing node or module is
claimed globally unnecessary. The main node's old 26 direct proof dependencies
are replaced by the three new subassembly nodes; the actual operation, tensor,
projection, point, domain, localization and common-stage inputs remain below
those nodes, rather than being claimed as completed or discarded. The geometric
restriction remains exactly the original Poincare fibre, and the unit route is
preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction of the source, target or existing DAG statement is
proposed. The existing nine-step natural-language proof has no single Lean lemma
that packages each required normalized family. In particular, ordinary scalar
adjunction and tensor reassociation search hits do not establish the geometric
comparison squares. The new statements expose the substantial construction work
that remains, with the original finite, completed, raw rational and common-stage
categories. They add no flatness or properness assumptions and no field-to-finite
reduction functor.

Self-audit of the new statements: identity and successive passages use the same
normalizations as the existing structure. Finite maps include nonflat quotients
such as Z/l^2 to F_l. Integral reduction uses every good representative, not a
selected witness; closure uses the same common-stage representative predicate.
The square hypotheses include all point normalizations and both comparison
composition laws, so arbitrary sign-twisted comparison maps cannot be substituted.
Zero inputs, the geometric point case, exponent one, equal fields, and identity
passages introduce no extra hypotheses or degenerate construction requirements.
No independent second reader is claimed; the dispatcher explicitly forbids agents.

## New nodes

`lem-sf-mixed-cup-operation-comparisons` isolates steps 2--5, 7 and 8: construct
actual scalar mates for both support choices, apply point sections, then obtain
normalized identity and composition maps. Its proof retains the finite etale
origin transport, completed finite-free argument, raw rationalization and common
finite-stage passage. Its statement does not mention cup or site tensor data.

`lem-sf-mixed-cup-tensor-comparisons` isolates the site tensor part of steps 2--4,
8 and 9: the canonical finite balancing map, completed scalar comparison,
Roos reduction comparison on every good representative, raw localization,
rational scalar extension and common-stage representative. Naturality and the
formal passage recursion give its laws, independently of cohomology.

`lem-sf-mixed-cup-square` isolates steps 5--9: paste coefficient/projection
compatibility with the ordinary counit mate equation; apply the point fibre;
then use identity/composition coherence for the formal passage recursion. Every
comparison and normalization is an explicit hypothesis, supplied in the main
proof by the other two lemmas. It asserts only an equality of existing morphisms.

All nodes cite the latest blueprint mixed-cup definition and the corresponding
parent proof steps. LeanSearch, LeanFinder, Loogle, Mathlib grep, project rg and
blueprint/DAG searches found ordinary balancing tools and existing definitions,
with no theorem for these normalized subassemblies. The source and full argument
are recorded in each theorem docstring and node. No change record is required:
existing public signatures and definitions remain verbatim.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
