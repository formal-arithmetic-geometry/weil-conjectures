## What changed

Replaced the assigned theorem's single sorry by a complete categorical assembly.
The statement and every existing public declaration are unchanged. The proof uses
private imports of NativeOpenTensorUnitNormalization, the two new modules below,
and MapDerivedCategoryMate. No existing module besides the item is changed.

The private helpers prove that exact localization preserves the specified unit
square, that the ordinary derived open unit is invertible, and that the adjunct
of tensor(unit,id) followed by restriction inverse is a natural isomorphism when
tensor preserves open support. A further helper proves the full forward forgetting
square from the native and ordinary inverse-unit equations and the restriction
square. The final proof constructs gamma′ and packages every record field. A private
unit-square predicate prevents expansion of the large localized adjunction during
specialization; the exact derived functor is locally irreducible in that proof.
No shared definition or exported attribute is changed.

Validation: lcompile.py --all compiled all three final modules without warnings:
restriction comparison 13.3 seconds, ordinary support 4.8 seconds, and the assigned
module 26.2 seconds. A direct text comparison confirms that the original public
theorem signature is unchanged. Every delivered Lean line is at most 100 characters.

## Proved and sorry left

Closed the one original hole in
AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_forget_normalization.
The item itself has zero sorries. This is a decomposition, not a completed proof
of the geometric assertion: two strictly smaller public holes are added:

- AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_restriction_forget,
  node lem-sf-native-open-tensor-restriction-forget. Only the restriction/tensor
  comparison and its forgetting square are asserted. The hypotheses omit the
  supplied extension and gamma identifications; the conclusion has no gamma′,
  inverse-unit equation or open gamma forgetting square.
- AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_open_tensor_support,
  node lem-sf-native-ordinary-open-tensor-support. Only invertibility of the
  ordinary counit on tensor(E′ M,N) is asserted. It has no native data, rho,
  gamma, presentation or forgetting compatibility hypothesis or conclusion.

The existing native_open_tensor_unit_normalization is used without alteration;
its remaining hole is not added by this delivery. All private helpers are proved.
There is one original hole closed and two holes added; the net is minus one.

## No longer needed

No original import is removed and no module is withdrawn or claimed globally
pruned. The direct proof edges to lem-sf-weil-native-closed-forgetful and
lem-sf-weil-frobenius-action-resolutions move to the restriction comparison
obligation. They remain needed there and in the fixed native definitions.
The original direct use of lem-sf-open-tensor-normalization is unnecessary for
the assembly: construct the ordinary comparison from support and its unit
transpose. The support obligation uses the smaller lem-sf-open-tensor-support
route, which retains the ordinary open-support geometry. The unit route is kept.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original one-step plan suppressed the distinction
between restriction compatibility, ordinary open support and the categorical
uniqueness argument. The latter is now formal Lean, including the exact-derived
unit comparison; the two geometric parts remain explicitly assigned statements.
The earlier normalization splits are not repeated under new names.

Both new statements were checked on zero inputs, the empty open and the identity
open. Restriction is a strong tensor comparison for the geometric open; support
holds because tensoring an object extended from that open again gives an object
in the extension's essential image. No boundedness or flatness of the arbitrary
derived input is assumed: K-flat representatives supply the total-tensor proof.

## New nodes

lem-sf-native-open-tensor-restriction-forget records the restriction square in
NativeOpenTensorRestrictionForget.lean. Its source is Stacks 0GL1/0E8I/015F,
with representative normalization provided by the existing presentation. Three
kinds of Mathlib search found no existing native derived comparison theorem.

lem-sf-native-ordinary-open-tensor-support records the support consequence in
NativeOrdinaryOpenTensorSupport.lean. Its source is the ordinary open tensor
argument in Stacks 0GL1 and 0E8I. Mathlib supplies the essential-image/counit
criterion but not this geometric support statement. No change record is needed:
existing public interfaces are unchanged and only the item's own node is updated.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOpenTensorForgetNormalization": "3fd4b9f7f6f6ee071fdf4e542482e3632ec028a7", "Sheaf.Paper.NativeOpenTensorRestrictionForget": "116931089bf6240899180d4edef5def0e43b5283", "Sheaf.Paper.NativeOrdinaryOpenTensorSupport": "d765d413a042e76d319b1f73f29795ee3dd7230c"}, "results": {"Sheaf.Paper.NativeOpenTensorNormalization": {"hash": "f08a9fdb0425acbb38206b2e3d9a405a8d3b8729", "status": "OK"}}, "seconds": 73, "time": "2026-10-28T12:33:31+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
