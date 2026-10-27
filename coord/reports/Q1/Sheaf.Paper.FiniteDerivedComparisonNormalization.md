## What changed

Proved `CategoryTheory.FiniteDerivedComparison.tensorComparison_coefficients` without
changing its statement. Added the proof-only import
`Sheaf.Paper.NormalizedCoefficientTensorSquare`, whose single public theorem
`CategoryTheory.NormalizedCoefficientTensor.normalizedCoefficientTensorSquare` is fully
proved. It takes the four existing derived functors, counits and universality proofs
explicitly. The item applies it to its `Pullback` fields.

For each edge, canonical tensor normalization supplies the tensor isomorphism. On
flat-term K-flat representatives all four edge counits and both composite counits
are invertible. Unary comparison descent produces the scalar-association isomorphism
and proves its representative normalization and uniqueness. The proof pastes the
two tensor squares on each route, cancels the invertible computation maps, and uses
the existing cochain coefficient identity. Fully faithful restriction to resolving
pairs extends this equation to all unbounded derived inputs.

The coefficient argument was first implemented within the item. Profiling showed
substantial kernel checking of the native total-tensor presentations and a combined
compile over 60 seconds. The proof uses the existing irreducible tensor presentations,
cached instances, and explicit functor and universe parameters. The completed
coefficient argument was then moved to its own module, using raw functors and
counits to avoid repeatedly unfolding a right-extension package. The existing private resolving-pair restriction argument was also extracted into
`Sheaf.Paper.DerivedResolvingPairRestriction`, with the fully proved public theorem
`CategoryTheory.derivedResolvingPairRestriction`. Both proof modules import it, so
its proof is checked once. No shared definition or instance was changed. The DAG now records this proof, including the already
separate coherence/composition components and the identity/pasting specialization.

## Proved and sorry left

Closed one of the item's three original holes:
`CategoryTheory.FiniteDerivedComparison.tensorComparison_coefficients`
(node `lem-pur-finite-derived-comparison-normalization`).

Added zero holes. The new resolving restriction theorem
`CategoryTheory.derivedResolvingPairRestriction`
(node `lem-pur-derived-resolving-pair-restriction`) is proved. The new theorem
`CategoryTheory.NormalizedCoefficientTensor.normalizedCoefficientTensorSquare`
(node `lem-pur-normalized-coefficient-tensor-square`) and all its private helpers
are proved. This is a proof from the project's existing declared dependencies,
not a decomposition into new sorry statements.

The two remaining holes are unchanged:

- `CategoryTheory.FiniteDerivedComparison.tensorComparison_coherence_associator`
  (`lem-pur-finite-derived-comparison-normalization-associator`).
- `CategoryTheory.FiniteDerivedComparison.tensorComparison_coherence_unit_symmetry`
  (`lem-pur-finite-derived-comparison-normalization-unit-symmetry`).

Validation: all three sandbox modules compiled through `lcompile.py --all`: the
restriction lemma in 1.7 s, the coefficient module in 48.5 s, and the item in 54.8 s.
The delivery tool runs final preflight against the complete packet.
The completed argument uses no boundedness or coefficient-flatness assumption.
It does not invert a coefficient map or a quotient transition. In particular,
identity changes, zero coefficients, and nonflat quotient changes use the same
ordinary scalar-association identity and resolving descent.

## No longer needed

The direct proof import `Sheaf.Paper.ResolvingRepresentativeWhiskering` was
replaced in the item by `Sheaf.Paper.DerivedResolvingPairRestriction`; it remains
needed transitively by that specialization. No module is withdrawn or globally
pruned. The
coefficient argument does not require constructing a full derived monoidal System:
it uses the existing canonical tensor normalizations and unary comparison descent.
The general monoidal-comparison node remains below the unfinished unit/symmetry
component and is not claimed to be globally unnecessary.

The root node now cites its own associator, unit/symmetry and compositor components
when combining those clauses, and cites the completed coefficient-square node for
the coefficient clause. The lower normalization, cochain, K-flat, and descent
nodes are still needed by those components and by the new proof. Its unit has no
realized statement or proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The latest blueprint ancestor is shorter than its imported expanded DAG statement;
its finite-reduction and scalar-extension compatibility still needs the
coefficient square proved here. No blueprint or target statement is changed.

The root DAG still described a direct application of the full monoidal System
lemma for coherence, although the current Lean proof combines two separately named
open components. Its revised proof records those components. The coefficient
argument required no mathematical correction and no signature change.

The separate new theorem is fully proved, so the module split relocates completed
proof code and adds no mathematical obligation. All original target, public
signature, and public definition data are preserved.

## New nodes

`lem-pur-normalized-coefficient-tensor-square` records the completed argument for
four universal derived pullbacks with explicit cochain counits. Its source is
Stacks `sites-cohomology.tex`, Tags 07A4, 0G7E and 0D6D, together with the existing
balanced coefficient identity. The proof has five steps: edge normalization,
unary descent, elementary pasting of representative squares, the cochain equation
with cancellation, and fully faithful restriction. Its Lean module contains one
public theorem and no sorry. This is the coefficient clause of the parent proof,
not a replacement of the unit route.

Whole-blueprint searches for "coefficient square" and "scalar association" both
returned zero matching blueprint nodes. The nearest blueprint ancestor is
`def-weil-frobenius-coefficient-twists`; its current blueprint sentence requires
compatibility with finite reduction and scalar extension. The imported expanded
node called this clause 5. LeanSearch returned ordinary
Kaehler/flat base-change results, Loogle returned generic CoreMonoidal constructors,
and msearch grep returned zero matches. The existing project descent and cochain
theorems are used rather than introducing new assumptions.

`lem-pur-derived-resolving-pair-restriction` extracts the existing private proof
from the item into one fully proved public theorem. It passes from cochains to
homotopy objects, applies the existing resolving-representative restriction, and
transports back along the quotient comparison in each variable. Whole-blueprint
searches for "resolving" and "fully faithful" returned three and 26 entries; none
is this cochain specialization. LeanSearch returned derived-transform/restricted
adjunction results, Loogle found generic localization whiskering, and msearch
grep returned zero hits. The project general theorem supplies the proof. No
change record is needed: existing public signatures and definitions are unchanged.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
