## What changed

Replaced the proof hole in `CategoryTheory.ConstantCompletion.koszulQuotientAugmentation_isIso`
without changing its signature, its public import, or any coefficient definition. The proof
uses the existing Noetherian algebraic Koszul pro-zero theorem, transports derived-zero
transitions through an exact functor, transports them through K-flat tensor, and applies the
existing right-derived-limit universal-property helper to exactly the specified `rlim`.

Added `ConstantExactCoefficientRealization`: 405 lines of ordinary coefficient realization
and its scalar and quotient normalization proofs. The functor is the actual constant module
functor followed by ordinary change of rings. The inverse of its quotient comparison is
constructed by sectionwise linear descent through the finite projection. No data is chosen
from an unproved existence assertion. Its generic generator argument adapts the proved
finite argument in `AdicResidueExactCoefficientRealization` to this arbitrary small site and
both Boolean coefficient choices.

Added two finite comparison interfaces in their own modules. The coefficient-cone interface
takes the exact realization and its normalized regular/quotient isomorphisms as explicit
inputs. The tensor-cone interface has no Noetherianity or flatness hypothesis. Neither asserts
eventual vanishing or a derived-limit conclusion. All new imports of the item are proof-only.
No existing module besides the assigned item is changed.

## Proved and sorry left

Closed the item's one syntactic hole:
`CategoryTheory.ConstantCompletion.koszulQuotientAugmentation_isIso` now has a complete proof
from the finite comparison statements and existing declarations. The private
`proZero_of_exact_realization` is proved, including localization of zero and conjugation by
the strict comparison isomorphisms.

`CategoryTheory.ConstantCompletion.constantExactCoefficientRealization` and all its private
helpers are proved with zero local holes. In particular, the regular-module isomorphism is
proved by the coyoneda criterion and both inverse identities for the quotient comparison
are proved from the actual projection surjectivity/kernel formulas.

Added two holes, each exactly `:= by sorry` in a public named theorem:

- `CategoryTheory.ConstantCompletion.constantKoszulCoefficientConeComparison`, node
  `lem-r1-constant-koszul-coefficient-cone-comparison`.
- `CategoryTheory.ConstantCompletion.constantKoszulTensorConeComparison`, node
  `lem-r1-constant-koszul-tensor-cone-comparison`.

This is a decomposition, not a claim of a net proof: one upper hole closed and two strictly
smaller finite holes added (net -1). The item has zero remaining local holes; the packet has
two. The first remaining obligation concerns only the coefficient complex and strict finite
cone identifications, with an explicitly supplied exact realization. The second concerns
only ordinary strict tensor/cone identifications. The combination proving pro-zero transport
and invertibility of the specified derived limit is fully written in Lean.

The final file set was compiled in import order through `lcompile.py`. Before the final
proof-only import cleanup, the four file times were 0.0 seconds (cached exact realization),
8.1 seconds, 2.7 seconds and 32.9 seconds, with no warnings or errors. Delivery runs the final
compile and preflight again.

## No longer needed

No existing module is withdrawn, and no existing public import is removed. No globally
pruned module is claimed.

The original parent's direct planned dependencies on
`def-weil-pbc-ringed-koszul-system`, `lem-u4-constant-koszul-quotient-augmentation`,
`lem-weil-pbc-constant-module-section-properties`,
`lem-weil-pbc-sectionwise-adic-algebra-limit`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and
`lem-weil-pbc-localization-universal-property` are replaced in its proof record by the
finite comparison interfaces and the proved API of `FlatConstantTensorProZeroCones`.
These ingredients remain used by the finite steps or by the generic helpers; this is
reorganization of direct dependencies, not a claim that their mathematics is unneeded.
The termwise-flat hypothesis stays verbatim, although the generic K-flat tensor transport
already suffices for the final argument.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no statement repair is proposed. The existing scheme/site
specializations of coefficient realization and tensor-cone comparison do not directly type
check for the arbitrary small site here. Importing the adic-residue specialization would
also bring in the constant-completion equivalence that reaches this item. The finite
ordinary realization argument was therefore adapted locally with proved private helpers.

The attempted direct finite coefficient-cone proof exposed an additional identity-component
comparison: `ringedKoszulTensorTowerComplex` reconstructs its levels using
`CochainComplex.of`, so its level complex is not definitionally the original total tensor
complex. The remaining finite node's proof explicitly records the required natural
identity-component isomorphism before the tensor unitor. This is finite chain-level glue,
not another pro-zero or derived-completion assertion.

## New nodes

`lem-r1-constant-exact-coefficient-realization` records the proved ordinary coefficient
realization, regular module comparison, and normalized finite quotient comparisons. Its
edge cases include the zero and unit ideals, zero rings, and empty sites.

`lem-r1-constant-koszul-coefficient-cone-comparison` records the remaining finite exterior
realization and augmentation normalization square, followed by the already available
additive cone-family comparison. It has no arbitrary complex, K-flatness, eventual
vanishing, or derived-limit claim.

`lem-r1-constant-koszul-tensor-cone-comparison` records the remaining strict tensor/cone
isomorphism for any normalized augmentation. Its proof uses the zero-summand law, the
invertible degree-zero Koszul unit, scalar tensor balancing, and the signed tensor-cone
formula. It has no Noetherianity, flatness, or derived-limit claim. No change record is
needed because only the item and new modules/nodes are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantExactCoefficientRealization": "f64ea64e14426cde29409a18c146327c4647ee1f", "Sheaf.Paper.ConstantKoszulCoefficientConeComparison": "f0b78eab3b58d5d0c18772c3617ee439758da99c", "Sheaf.Paper.ConstantKoszulQuotientAugmentationIsIso": "45df59bb4ee1147ba34a3387a01fdc2ba290afaf", "Sheaf.Paper.ConstantKoszulTensorConeComparison": "bf6d27b36a1ec223a41bb1e95a3da48926e2a4c9"}, "results": {"Sheaf.Paper.ConstantCompletionKoszulQuotientComparison": {"hash": "a98b9f41b6b39169b3d323a0856f3eb048867305", "status": "INFRA"}}, "seconds": 135, "time": "2026-10-28T12:19:02+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
