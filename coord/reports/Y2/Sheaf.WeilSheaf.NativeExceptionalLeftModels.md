## What changed

Implemented `native_exceptional_left_models` with its original signature. The proof now:

- proves that derived forgetting followed by closure transport is bounded constructible,
  using inverse pullback along the closure isomorphism;
- constructs every `ForgetModel` on all derived morphisms using Mathlib's fully faithful
  essential-image factorization and the specified realization family;
- obtains the normalized cyclic Hom boundary data;
- proves the native Hom bijection by an additive short five lemma, retaining the
  degree minus one coinvariants and passing between ambient and full subcategory
  morphisms.

Added `Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares` for the remaining geometric
assembly: the normalized comparison, counit lift, additive outer equivalences, and the
boundary and forgetting squares. This theorem does not assert the middle Hom bijection
or construct the ForgetModels; the assigned module supplies both of those steps.
No existing public declaration, definition, signature, attribute or public import changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_left_models`
(node `lem-sf-native-exceptional-left-models`). Its complete Lean proof is from the
named constructibility, cyclic boundary, and geometric counit steps.

Added one hole:
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_counit_hom_squares`
(node `lem-sf-native-exceptional-counit-hom-squares`). Its proof is exactly `by sorry`,
with source and a complete proof plan in the docstring and node. There are zero holes
in the assigned module and one in the new module. Closed 1, added 1: this is a
**decomposition**, not a net hole closure or an axiom free completion.

The proved private helpers are `underlying_constructible`, `forget_models`, and
`short_five_bijective`. They contain no holes. The final chase explicitly proves
injectivity and surjectivity on the full native derived Hom groups; it does not assume
that derived forgetting is faithful.

Validation: `lcompile.py --all` compiled both delivered modules cleanly, exit code 0.
The assigned module contains zero `sorry` tokens and the new module contains one.

## No longer needed

None. No existing module or declaration was withdrawn. The original geometric
open/proper, scalar normalization, constructible realization and cyclic theory
dependencies remain needed, some through the new geometric assembly node. The
cohomology comparison and constructible pullback declarations are generic tools inside
the model construction argument; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The geometric assembly requires matching the actual native
hearts, closure transports, section presentations, scalar normalized mate and finite
composite boundary compatibility before the generic cyclic counit theorem applies.
This application is isolated with the two precise outer square equations; the
constructibility/factorization and final short five steps are formalized.

Checked edge cases: zero complexes and empty schemes give zero outer groups; identity
compactifications give the identity adjunction maps. In particular, the negative degree
coinvariants are retained. The new theorem permits any ForgetModels with their specified
realization isomorphisms; full faithfulness identifies them with the same underlying
presentation, so no extra choice or model normalization hypothesis is added.

## New nodes

`lem-sf-native-exceptional-counit-hom-squares`, in
`dag/nodes/sec-six-functors/lem-sf-native-exceptional-counit-hom-squares.json`, is the
normalized geometric counit and its two outer cyclic Hom squares. Its statement uses
the actual native Frobenius coinvariant and invariant groups and their supplied
normalized boundaries, not unspecified auxiliary groups. It omits the middle native
Hom bijection. The assigned module constructs the models and proves that omitted
bijection from exactness. This is a genuine step of the existing argument rather than
the original existential/universal property under another name. LeanFinder, Loogle and
Mathlib grep found no exact match; local searches found the generic cyclic theorem but
no assembled native/common stage comparison.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
