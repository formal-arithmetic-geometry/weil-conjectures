## What changed

Marked `native_weil_tensor_ringed_derived_square_native_coherence` as
`STATEMENT-DISPUTED` and annotated the existing node's proof plan with the
specific missing normalization. The theorem's signature and its existing
whole-proof `sorry` are unchanged. No definition, instance, public import,
source-library declaration, or target was changed.

Added the proved private theorem
`symmetric_scalar_tensorator_obstruction` to the item module, with a private
proof import of `Mathlib.Tactic.NormNum`. It checks a precise obstruction to
the inference used in the plan. This delivery is a statement/proof-plan audit,
not a proof of the assigned geometric theorem or a decomposition of its hole.

Validation: the delivered item compiled through `lcompile.py` in 16.1 seconds
with exit code 0. The scalar check has a complete Lean proof. The public
signature and imports seen by consumers are unchanged.

## Proved and sorry left

Closed: zero of the one original holes. Added: zero holes. Split off: zero.

The proved private `symmetric_scalar_tensorator_obstruction` asserts the
existence of nonzero rational scalars c(p,q), symmetric in p,q and equal to 1
when either degree is zero, for which

    c(1,1+2) c(1,2) != c(1+1,2) c(1,1).

Take c(1,1) = -1 and c(p,q) = 1 otherwise. The two sides are 1 and -1.

The only hole left is
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_coherence`
(node `lem-sf-native-weil-tensor-ringed-derived-square-native-coherence`). Its
original statement is retained for independent semantic review.

## No longer needed

None. No existing import, module, declaration, node attachment, or dependency
was pruned or withdrawn. The existing item remains required by
`NativeWeilTensorRingedDerivedSquareNative`. The unit route is unchanged.
There are no new nodes.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the proof plan treats identification of the ordinary
representative tensor with S.tensor as an identification of their monoidal
constraints. The supplied interfaces do not record that identification.

The precise interfaces read are:

* `CoefficientClosedStructure` supplies a monoidal structure, chosen
  tensor-right adjunctions, and naturality of evaluation in the Hom source.
  Its evaluation and transpose depend on those chosen adjunctions.
* `NativeHomRepresentatives` supplies natural isomorphisms to product-total
  Hom complexes. It does not normalize them against internal composition,
  the tensor associator, or the unit.
* `NativeAdjunctionNormalization` normalizes ordinaryModel against the
  chosen transpose and chosen Hom representatives. Those are variable
  inputs, so this does not identify ordinaryModel with the fixed canonical
  localization tensorator.
* `NativeOrdinaryTensorModels` adds a signed swap and the braiding square
  on K-flat pairs. It has no representative associator or unitor equation.
* `hmonoidal` identifies S.monoidal with the standard monoidal structure.
  It does not identify a chosen isomorphism from its tensor to a total
  tensor with the canonical localization comparison.
* `_hnaturality` supplies naturality, and `hforget` identifies t with this
  chosen ordinaryModel. Neither adds an ordinary associator equation.
* `d.coherence` gives the ringed equations. Moving them to the stated target
  requires a coherent ordinary tensor identification, which is precisely
  the step not supplied by the above data.

The scalar check illustrates the logical distinction even with normalized
units. In a category of graded vector spaces, a symmetric degreewise
rescaling c(p,q) is a natural invertible tensor comparison and commutes with
the signed braiding. Associativity additionally requires the cocycle equation

    c(p,q+r) c(q,r) = c(p+q,r) c(p,q).

The displayed c fails it. Naturality and preservation of the signed swap
therefore cannot, by themselves, justify the missing associator step.
Choosing adjunctions does not remove this issue: an invertible natural
rescaling of a left-adjoint tensor functor transports its adjunction, so
uncurrying must be pinned to an independently fixed tensor model to impose
such a normalization.

Scope of the evidence: the compiled lemma proves the scalar obstruction,
not a formal counterexample to the full theorem on the specific native
sheaf categories. No claim is made that a particular natural noncocycle
rescaling on those categories has been constructed. An additional rigidity
argument specific to those categories might settle the original statement,
but it is absent from the plan and from the four stated proof dependencies.
This is the reason for requesting semantic review, rather than claiming a
formal refutation or stating more unverified transport lemmas.

A concrete repair to investigate is to normalize the ordinary model against
the canonical construction already used in
`NativeOrdinaryTensorRepresentatives`: its private `ordinaryModel` is the
canonical lax localization tensorator followed by the localized inverse of
`ordinaryTotalIso`. That explicit normalization, or representative
associator and unitor equations transported from it, would supply the missing
input. `native_ordinary_closed_tensor_models` already constructs its witness
from that canonical model. The generic hS interface currently forgets the
additional information. This audit does not add hypotheses or change that
shared definition, since the compatibility of all of its consumers must be
reviewed together.

Searches completed with `msearch.py`: LeanFinder found Mathlib's monoidal
and symmetric equivalence transport machinery; Loogle returned no result
for `Functor.CoreMonoidal`; grep found generic oplax/monoidal constructors
and transport. The apparent exact native transport theorem imports the
parent derived-square theorem and cannot be used here without an import
cycle. The four planned proof dependencies and their Lean declarations were
read. None states the missing ordinary representative constraint equality.

The current server queue row was checked over ssh: the item is a stage-3
`proof` item with one hole, not a zero-hole repair or quarantine. There was
no current matching rework row or build-error file. The shared H4 return
contains only the old general upstream-sync notice.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence": "c1d844b0efd4627628b4c1765b262973ced5fff5"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": {"hash": "c8e550c2ce0b12dcf0b74ffb1011fa65c7b46ce0", "status": "OK"}}, "seconds": 108, "time": "2026-10-28T07:59:36+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
