## What changed

Replaced the proof hole in `Sheaf.SixFunctors.OpenStrictScalarTransport` by assembly
from two strictly smaller statements: finite generator-normalized scalar comparison,
and compatibility of those finite maps with quotient transitions. The assembly uses
`SemilinearSections.systemIsoOfEvaluation_exists`, already proved in
`Sheaf.Paper.SemilinearSystemIsoAssembly`.

The item constructs one natural isomorphism of actual strict systems. Naturality is
proved by joint faithfulness of finite evaluation. Its evaluated comparison equals
the finite comparison by cancellation of the three recorded evaluation isomorphisms;
the desired generator formula is then the finite generator formula.

Added `OpenFiniteScalarComparison` and `OpenScalarTransitionCompatibility`. The latter
also defines `scalarLevelComparison`, an explicit composite of supplied isomorphisms.
All added imports of the item are private proof imports. Existing public signatures,
definitions and imports are unchanged. No shared existing module was changed.

Local reduction attributes keep scalar adjoints and coefficient-sequence constructions
closed during component comparisons, while exposing the equal coefficient interfaces.
These attributes are local to this file; no shared reducibility attribute was changed.

Validation: remote compilation succeeded for the two new modules (46.6 s and
45.5 s), and for the cleaned item (15.7 s, exit code 0, no warnings). A text
comparison checked that the original theorem signature, the existing definition body,
and all public imports are unchanged. All files remain within the 100-character limit.

## Proved and sorry left

This is a decomposition, not a completed proof of the original mathematical obligation.
The original module had one hole and now has zero. The delivery adds two holes, so its
net hole change is minus one (one closed minus two added).

Closed by a complete Lean reduction:

- `WeilConjectures.OpenSemilinearTensor.openStrictScalarTransport`
  (`lem-sf-open-strict-scalar-transport`).

Remaining new holes, each in its own module:

- `WeilConjectures.OpenSemilinearTensor.existsUnique_openFiniteScalarComparison`
  (`lem-sf-open-finite-scalar-comparison`): existence and uniqueness of normalized
  finite comparisons only. It has no ordinary reductions AX/AU, strict-system
  comparison, or transition assertion.
- `WeilConjectures.OpenSemilinearTensor.openScalarTransitionCompatibility`
  (`lem-sf-open-scalar-transition-compatibility`): a quotient-square equality for
  supplied finite normalized maps. It constructs no finite comparison and no
  strict-system morphism or isomorphism.

Neither split restates the original existence of a normalized strict comparison.
The first determines its finite data, and the second checks the extra horizontal
naturality needed to assemble them. The remaining assembly and final normalization
are proved in the item.

No definition contains a hole. The finite comparison datum is selected from a unique
existence theorem; all its maps are determined by the scalar-unit generator condition.
The system isomorphisms are selected from the existing proved assembly theorem and
are determined by their evaluations.

## No longer needed

No pre-existing import was removed and no module is withdrawn or pruned.

The original direct dependency on `lem-sf-semilinear-slice-scalar-generators` is
replaced in this item's proof by the finite transport and transition-square nodes.
It remains a dependency of the finite transport node: only its coefficient-linear
components and generator normalization are needed there. Its separate unbounded
chain comparison and augmentation fields are not needed by this item. The previous
plan to construct three separate comparison isomorphisms between entire generic
systems and the supplied ordinary systems is replaced by existing system assembly.

## Where the brief, the DAG or earlier work was wrong

The original DAG classified the comparison of actual finite scalar extensions with
the slice models and its compatibility with every quotient as elementary. These
are substantial transport calculations. The split makes the two calculations explicit
while preserving the scalar normalization and every quotient index.

No statement was disputed or weakened. The proposed finite maps are uniquely fixed
by their scalar-unit generator formula, using injectivity of the scalar and open
adjunction Hom equivalences. The transition argument also covers m=n (identity),
the zero module and the empty open: no extra nonemptiness, flatness, completeness,
quasi-compactness or boundedness hypothesis was introduced. The unit route is unchanged.

## New nodes

`lem-sf-open-finite-scalar-comparison` is the finite-level specialization and
coefficient-equivalence transport of the existing scalar generator theorem, sourced
to Stacks 03DI, 03EK and 0E8I. It supplies a uniquely determined finite comparison
family, without quotient compatibility. LeanFinder, Loogle, LeanSearch and source
grep found general adjunction APIs but no existing normalized comparison of these
supplied open transports.

`lem-sf-open-scalar-transition-compatibility` is the quotient-square step, sourced
to the same extension and scalar adjunctions and the strict quotient system preceding
Stacks 0941. Its proof uses AX/AU quotient equations, the recorded open-system unit
evaluation, and identity restriction evaluation. The same searches found no exact
statement. It reuses the existing ordinary reduction and finite comparison interfaces.

No change record is needed: only the item, its proof node, and the two new modules
and their nodes are changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
