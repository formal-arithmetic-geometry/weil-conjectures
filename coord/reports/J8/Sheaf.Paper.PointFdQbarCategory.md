## What changed

Proved both original holes in Sheaf.Paper.PointFdQbarCategory without changing
any existing signature or definition. DerivedCategory.pointFd_shift_mem uses the
homology shift isomorphism, translation of finite support and invariance of finite
dimension under linear equivalence.

DerivedCategory.pointFdQbarCocone_isFilteredTwoColimit now proves its three fields.
Object surjectivity follows from the stored stage pair. Hom-injectivity uses a
proved natural retraction of extension followed by restriction of scalars, descended
through localization. Hom-surjectivity uses DerivedCategory.pointFd_morphism_descent
in the new module Sheaf.Paper.PointFdMorphismDescent, which is fully proved.

The new descent proof chooses finite bases of the cohomology spaces and a finite
coefficient field containing all matrix entries on the finite support. It constructs
the maps over that field explicitly, verifies extension on basis vectors, and uses
the existing cohomology Hom-bijection to lift the resulting family to a derived
morphism. The existing normalized cohomology/tensor tower identity verifies the
required equality. Private helpers are all proved. The tower helper uses the
ordinary tensor comparison directly; explicit unfolding at the final application
avoids an unnecessary equality transport and the earlier elaboration failure.

Proof-only imports in the item are the derived exact-functor composition API,
linear dual lemmas and the new descent module. The descent proof additionally uses
the existing scalar/cohomology comparison, field cohomology splitting, tensor bases
and finite-dimensional basis API. All existing public imports are retained.

## Proved and sorry left

Original holes closed, both by complete proofs:
- DerivedCategory.pointFd_shift_mem.
- DerivedCategory.pointFdQbarCocone_isFilteredTwoColimit.

The new DerivedCategory.pointFd_morphism_descent is also completely proved; its node
is lem-weil-point-fd-morphism-descent. No holes are added or left in either delivered
module. This is two original holes closed, zero lower holes added, net reduction two.
The proof uses the existing stated field_complex_cohomology_splitting theorem and
the normalized scalar/cohomology comparison declarations; their independent proof
obligations remain in their existing modules, as intended in stage 3.

## No longer needed

No original import is removed: all four public imports serve existing statements
or definitions. No original proof dependencies were listed in the definition node.
No existing node or module is claimed as pruned.

Hom-injectivity does not need cohomology splitting or matrix equality: the natural
retraction proves faithfulness for arbitrary derived vector spaces, without any
boundedness or finite-dimensionality hypothesis. Those tools are used only for
Hom-surjectivity. General affine perfect-complex object descent and bounded graded
family descent are not imported: finite matrix descent suffices here.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite two theorem holes in its realization.
Its copy now records the complete combination and the shift argument. There was no
existing stated common-field morphism descent theorem among its dependencies; the
new theorem supplies that part and is proved in this delivery. No existing statement
was judged false or changed.

The previous retained report described morphism descent as still open. This session
compiled the normalized finite-family construction and completed its final derived
comparison. Earlier scratch experiments are outside lean/ and are not delivered.

The new node uses lem-trf-field-complex-cohomology-splitting only as a generic field
linear algebra tool, namely its cohomology Hom-bijection. This proposed tool use is
recorded in split_report for independent review; no maintainer approval is added.
The source displays agree at old order 1509 and current order 1868. The unit
sk-def-sf-admissible has no proof steps or realized nodes; its route is unchanged.
Empty support, zero-dimensional cohomology and equal fields are covered: outside
support the source is zero, empty matrix families need only the compositum, and
inclusions allow equality.

## New nodes

lem-weil-point-fd-morphism-descent states descent of a single morphism to a common
finite coefficient field with the exact normalized tensor-tower conjugation. Its
new module Sheaf.Paper.PointFdMorphismDescent proves it completely by finite matrix
descent and the existing cohomology Hom-bijection. Its node records that argument
and the Lean statement. Retained LeanFinder, Loogle, LeanSearch and source-search
records found no exact match. The preflight detector flags the scoped `omit` on the new private helper as
an interface command. Its scope and unchanged public API are documented in
coord/changes/point-fd-private-helper-scope.md. No consumer adaptation is needed.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
