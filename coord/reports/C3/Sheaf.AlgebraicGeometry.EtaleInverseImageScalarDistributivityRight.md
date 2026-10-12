## What changed

Reduced `AlgebraicGeometry.etaleInverseImageScalarDistributivity_right` to the addition
comparison part of its recorded argument and proved the generic categorical transport part. Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition` and
`Sheaf.CategoryTheory.CartesianScalarDistributivityTransport`. The existing signature,
visibility, public imports, and docstring are unchanged.

The target proof establishes the canonical product isomorphism's projection identities,
identifies the source tensor-form action using the supplied formula for `muV`, proves its
scalar distributivity by `add_smul`, applies generic diagram transport with the supplied
addition compatibility equations, and rewrites target addition to sectionwise sums.
The original node now records these steps and their dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.etaleInverseImageScalarDistributivity_right`
(node `lem-weil-pbc-inverse-image-scalar-distributivity-right`).
The item's module has no remaining `sorry`.

Added one hole in a separate new module, with a complete proof plan in its docstring:

- `AlgebraicGeometry.etaleInverseImageComparisonAddition`
  (`lem-weil-pbc-inverse-image-comparison-addition`): identify ordinary addition with
  transported addition for the supplied compatible comparisons. This statement does not
  mention scalar action or distributivity.
Fully proved the new declaration `CategoryTheory.cartesianScalarDistributivityTransport`
(node `lem-weil-pbc-cartesian-scalar-distributivity-transport`). This transports an already
established source distributivity equation between arbitrary set-sheaf operations, assuming
explicit addition transport equations. It has no ring, module, or adjunction hypotheses. Its
proof identifies the two product comparison conventions, maps the source equation through
a monoidal functor, rewrites pairing and projections, and evaluates the target diagram.

This is a decomposition: one original hole closed, one added; net zero. It is not a claim of
a sorry-free target. The two private projection helpers in the target and all private helpers
in the generic transport module are fully proved. The target's source module law and its
specialization of the generic transport statement are fully proved. All three delivered
modules compile together without warnings through the prescribed `lcompile.py --all`.

## No longer needed

None. No existing import is removed. The algebraic-structures and conjugate-unit nodes remain
needed by the addition-comparison intermediate theorem. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The elementary final transport step hides substantial product
comparison calculations; it is now exposed as the generic transport item rather than left
as a hole inside the target proof; its generic categorical argument is now fully proved. The source law uses `add_smul`, with the original module
instance supplied explicitly because forgetting to sets hides its typeclass instances.

Edge cases: the addition-comparison theorem concerns sectionwise addition, uniquely fixed
by its formulas, and does not choose arbitrary ring or module data. Its proof does not assert
scalar laws. The generic transport theorem permits arbitrary operations and requires the
source equation explicitly; empty section sets and zero modules cause no exceptions, and
no monomorphism or surjectivity assumption on section maps is used. The prescribed
isomorphisms and finite-product preservation suffice for the categorical argument.

The local Stacks checkout is absent here. The cited proofs were read at
https://stacks.math.columbia.edu/tag/03D2 and
https://stacks.math.columbia.edu/tag/00YV; the additions to the proof plans expand their
finite-product transport argument. Search queries and actual results are in `searches.jsonl`.

## New nodes

`lem-weil-pbc-inverse-image-comparison-addition` records the comparison-compatible addition
part of the existing first step. Its module is
`Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition`.

`lem-weil-pbc-cartesian-scalar-distributivity-transport` records generic transport of a source
law through finite products, independently of any algebraic structures. Its module is
`Sheaf.CategoryTheory.CartesianScalarDistributivityTransport`.

The generic transport node is fully proved; only the addition-comparison node is left with
`:= by sorry`. No interface change records or forced adaptations are needed.

## Second reading by C3

1. Compared the delivered target module with the repository version. The theorem signature,
visibility, public imports, and docstring are unchanged; only proof-only imports, private
helpers, and the proof body were added.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile without
warnings. The target has no `sorry`; the only remaining `sorry` is the explicitly named
addition-comparison theorem, with a matching node and proof-plan docstring. No forbidden
axioms or unsafe declarations occur.
3. Checked the new statements against their formulas and edge cases. The addition theorem
asserts only sectionwise addition transport under the supplied compatibility hypotheses;
the generic theorem assumes the source equation and explicit transport equations and adds
no algebraic structure. Neither chooses data from an undetermined existence proof.
4. Read the proofs downward. The target uses the addition comparison node, the source
module law, and the generic transport node. The generic proof expands product comparison
and projection identities; no shorter existing library theorem was found. The imports are
needed for the statements or proof, and no old proof dependency can be pruned.
5. The unit route remains intact: the target node still realizes scalar-additivity through
the comparison-addition step and finite-product transport, and all node proof/proof_deps/
proof_origin fields match the Lean dependencies.

I changed only this report section; no Lean declarations or DAG fields were changed during
second reading.
