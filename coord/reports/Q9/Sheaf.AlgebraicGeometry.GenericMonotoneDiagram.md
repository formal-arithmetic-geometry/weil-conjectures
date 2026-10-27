## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.GenericMonotoneDiagram` by a complete
Lean reduction, preserving the theorem signature and the entire existing structure.
The proof obtains geometric chart data, applies homogeneous division to each prefix of
an arbitrary regular lift family, and proves supported formal generation and the
zero-ideal/empty-vertex implication.

Two new modules isolate genuine parts of the original seven-step plan:
`Sheaf.AlgebraicGeometry.GenericMonotoneVertexChart` contains the geometric construction
(original steps 1--4 and 7, using formal division to descend regular generation), and
`Sheaf.RingTheory.InitialExponentHomogeneousDivision` contains the finite triangular
homogeneous division argument (original step 5). Neither statement is the original
statement under another name: the geometric chart has no division assertions, while the
homogeneous statement is pure algebra with no scheme, chart, ideal, or monotonicity data.

The original module's proved private helper `exists_first_exponent` uses Mathlib's
well-founded degree-lex order. Its proved helper `supported_generation` applies the
existing `exists_unique_supported_formal_division`, proves that its remainder belongs
to the ideal, and rules out a nonzero remainder by its least exponent. This is the
original step 6, implemented for any ideal whose actual initial diagram is the generated
diagram. No new statement is required for this step. The empty-vertex argument is also
proved directly from the structure's vertex characterization and actual-diagram clause.

Validation: all three modules compiled together through `lcompile.py`. The initial
compile took 4.8 s, 2.3 s, and 7.1 s respectively; a new theorem's unused-Fintype warning
was fixed by using `Finite` instead. Final clean validation is performed by delivery.
The code handles zero variables, empty vertex families and prefixes, degrees below a
vertex degree, and nonclosed centers without adding assumptions. The homogeneous lemma
also permits repeated or unordered exponent lists: only the index set is ordered, and
later duplicate orthants have empty quotient regions. Over a field every nonzero first
coefficient is invertible, so coefficient-one normalization is unnecessary for that lemma.

Only this item's existing module and node, and the two new modules and their nodes,
are changed. All public imports of the existing module remain verbatim. No existing
consumer interface changes and no forced adaptations or change records are needed.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.HilbertCoefficient.genericMonotoneDiagram`
(node `lem-trf-generic-monotone-diagram`). There are zero direct holes left in the item.
The two private helper theorems and the assembly proof contain no holes.

Added exactly two named public theorem holes, each with a source, complete argument in
words, separate module, and DAG node:

- `AlgebraicGeometry.HilbertCoefficient.genericMonotoneVertexChart`
  (`lem-trf-generic-monotone-vertex-chart`).
- `MonomialDiagram.initialExponentHomogeneousDivision`
  (`lem-trf-initial-exponent-homogeneous-division`).

This is a decomposition: one original hole closed, two lower holes added; net -1
before any closure changes from proof-dependency imports. It is not a claim that the
geometric existence theorem or the homogeneous triangular-basis argument is proved.
The pre-existing `MonomialDiagram.exists_unique_supported_formal_division` remains a
used dependency with its existing hole (`lem-trf-supported-formal-division`); this
delivery adds no hole to that module. The new chart record consists of explicit fields,
with no data defined using an unproved existence witness and no hole inside a definition.

## No longer needed

Removed the item's proof import of
`Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`: its descent input now belongs
to the new geometric-chart node. Removed `Mathlib.Order.WellFoundedSet` and used
`Mathlib.Order.WellFounded` for the actual least-exponent argument instead.

The item's direct proof dependencies on `lem-trf-taylor-normal-cone-splitting`,
`lem-trf-graded-generic-initial-borel`, `lem-trf-monomial-upper-set-finite-basis`, and
`lem-trf-implicit-taylor-coordinate-calculus` are replaced by the new geometric-chart
node. These four nodes remain needed by that new node; no mathematical dependency or
library module is claimed pruned. `lem-trf-supported-formal-division` remains a direct
proof dependency. The new homogeneous division node isolates the former elementary
step 5 without adding unrelated infrastructure. No module is withdrawn. Pruned: none.

## Where the brief, the DAG or earlier work was wrong

No false statement, signature repair, or departure from the unit route was found.
The original step 5 was marked elementary, but its indexed finite-basis interface is
not supplied by the listed dependencies. It is now an explicit, strictly algebraic
intermediate theorem. The geometric inputs have declarations but do not yet directly
supply the affine chart and normalized regular lifts in the interface needed here;
the new geometric construction records that remaining composition precisely.

The source and module searches found no shorter existing theorem. In particular,
Mathlib's `MonomialOrder.div` supplies polynomial division using greatest terms; it
does not directly give uniqueness with the first-dividing-vertex supports in the
specified least-term homogeneous indexed family. The existing formal-division theorem
does give exactly the formal remainder needed here and is used without reproving it.

WANTED: Bierstone--Milman, Invent. Math. 128 (1997), sections 3.5, 7.1, 8 and proof of
Theorem 9.6, pp.278--279, for both new nodes. As in the owning node, the journal text is
not present in the repository literature; the new proofs in words are explicitly
marked as agent-written elaborations of the already reviewed owning-node plan.

## New nodes

`lem-trf-generic-monotone-vertex-chart` records the geometric chart with actual monotone
Taylor diagram and normalized regular ideal generators. It omits both universal
homogeneous and supported formal division and the empty-family conclusion. Its proof
keeps the existing Taylor normal-cone, generic Borel, Dickson, supported formal division,
and implicit Taylor calculus inputs. Its source is the geometric part of BM's first
proof paragraph of Theorem 9.6, as detailed in original steps 1--4 and 7. LeanSearch,
LeanFinder, Mathlib/project grep and blueprint searches are recorded in its node.

`lem-trf-initial-exponent-homogeneous-division` records original step 5 for any finite
linearly ordered index set, allowing direct specialization to each degree prefix. Its
proof is the finite triangular column argument, with the partition by first dividing
index made explicit. It requires no new proof dependency and no geometric existence
statement. Its source is BM (7.1), (7.2)(1)--(2), Lemma 7.7 and the owning node's step 5.
LeanSearch, LeanFinder, Mathlib/project grep and blueprint searches are recorded.

No change records are needed: no existing definition, signature, visibility, instance,
attribute, or public import is changed.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
